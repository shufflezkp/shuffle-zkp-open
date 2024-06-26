package main

import (
	"bytes"
	"fmt"
	"log"
	"math"
	"math/rand"
	"os"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	fr_bn254 "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/hash"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/test"

	cs "github.com/consensys/gnark/constraint/bn254"
)

const (
	// 5 private inputs
	PrivateItemNum = 60
	UniverseSize   = 10000
	//DummyVecLength   = 60
	ClientNum          = 1000
	CorruptedNum       = 500
	e                  = 2.71828182845904523536028747135266249775724709369995
	BN254Size          = 32
	CommitmentSize     = 32
	MaxNumOfCheckProof = 10
	TestRepeat         = 5
)

var file *os.File
var DummyVecLength uint64

func ComputeDummyNum(lambda uint64, n uint64, t uint64) uint64 {
	tmp := float64(2*lambda+254)/float64(math.Log2(float64(n-t))-math.Log2(e)) + 2
	return uint64(math.Ceil(tmp))
}

func PolyEval(vec []fr_bn254.Element, r fr_bn254.Element) fr_bn254.Element {
	prod := vec[0]
	prod.Add(&prod, &r)
	for i := 1; i < len(vec); i++ {
		tmp := vec[i]
		tmp.Add(&tmp, &r)
		prod.Mul(&prod, &tmp)
	}
	return prod
}

func PolyEvalInCircuit(api frontend.API, vec []frontend.Variable, publicR frontend.Variable) frontend.Variable {
	prod := api.Add(vec[0], publicR)
	for i := 1; i < len(vec); i++ {
		prod = api.Mul(prod, api.Add(vec[i], publicR))
	}
	return prod
}

type HistogramCircuit struct {
	PrivateX []frontend.Variable

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *HistogramCircuit) Define(api frontend.API) error {

	// just v
	tmp := frontend.Variable(1)
	for i := 0; i < len(circuit.PrivateX); i++ {
		for j := 0; j < len(circuit.PrivateX); j++ {
			if i != j {
				tmp = api.Mul(tmp, api.Sub(circuit.PrivateX[i], circuit.PrivateX[j]))
			}
		}
	}
	api.AssertIsDifferent(tmp, frontend.Variable(0))

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, circuit.PrivateX, circuit.PublicR)
	privateProd = api.Mul(privateProd, circuit.PrivateMask)
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	// checking commitment
	mimc, _ := mimc.NewMiMC(api)
	for i := 0; i < len(circuit.PrivateX); i++ {
		mimc.Write(circuit.PrivateX[i])
	}
	mimc.Write(circuit.PrivateMask)
	mimc.Write(circuit.PrivateSalt)
	api.AssertIsEqual(circuit.PublicCommitment, mimc.Sum())
	return nil
}

// generate a random element in fr_bn254
func randomFr() fr_bn254.Element {
	var e fr_bn254.Element
	e.SetRandom()
	return e
}

//type ClientSubmissionToShuffler struct {
//	PrivateVec [PrivateShareNum]fr_bn254.Element
//	DummyVec   [DummyVecLength]fr_bn254.Element
//}

type ClientSubmissionToServer struct {
	publicWitness *witness.Witness
	publicProd    fr_bn254.Element
	proof         *groth16.Proof
}

type ClientSubmissionToServerPlonk struct {
	publicWitness *witness.Witness
	publicProd    fr_bn254.Element
	proof         *plonk.Proof
}

type ClientState struct {
	PrivateX []fr_bn254.Element // the private X are the items
	PrivateY []fr_bn254.Element // the private Y are the dummies

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element

	PublicProd fr_bn254.Element
	PublicR    fr_bn254.Element
}

func (c *ClientState) Init(rng *rand.Rand) {
	c.PrivateX = make([]fr_bn254.Element, PrivateItemNum)
	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)

	// use rng to sample PrivateItemNum elements from the universe without replacement
	// the universe is [0, UniverseSize)
	// initialize a set
	sampled := make(map[uint64]bool)
	for i := 0; i < len(c.PrivateX); i++ {
		idx := rng.Intn(UniverseSize)
		for sampled[uint64(idx)] {
			idx = rng.Intn(UniverseSize)
		}
		sampled[uint64(idx)] = true
		c.PrivateX[i].SetUint64(uint64(idx))
	}

	// now generate the private dummy
	for i := 0; i < len(c.PrivateY); i++ {
		c.PrivateY[i] = randomFr()
	}

	// the privateMask is the product of privateY
	c.PrivateMask = fr_bn254.One()
	for i := 0; i < len(c.PrivateY); i++ {
		c.PrivateMask.Mul(&c.PrivateMask, &c.PrivateY[i])
	}

	//private salt is a random value
	c.PrivateSalt = randomFr()

	// the public commitment is the hash of the privateX, privateMask and privateSalt
	goMimc := hash.MIMC_BN254.New()
	for i := 0; i < len(c.PrivateX); i++ {
		b := c.PrivateX[i].Bytes()
		goMimc.Write(b[:])
	}
	b := c.PrivateMask.Bytes()
	goMimc.Write(b[:])
	b = c.PrivateSalt.Bytes()
	goMimc.Write(b[:])
	c.PublicCom.SetBytes(goMimc.Sum(nil))
}

func (c *ClientState) ComputePolyEval(publicR fr_bn254.Element) {
	prod := PolyEval(c.PrivateX, publicR)
	prod.Mul(&prod, &c.PrivateMask)
	c.PublicProd = prod
}

func (c *ClientState) GenAssignment(publicR fr_bn254.Element) HistogramCircuit {
	// first initialize all variables needed in the circuit
	PrivateX := make([]frontend.Variable, PrivateItemNum)
	for i := 0; i < len(c.PrivateX); i++ {
		PrivateX[i] = frontend.Variable(c.PrivateX[i])
	}

	// now compute the public prod
	c.ComputePolyEval(publicR)
	publicProd := frontend.Variable(c.PublicProd)

	// now create the assignment
	assignment := HistogramCircuit{
		PrivateX:         PrivateX,
		PrivateMask:      frontend.Variable(c.PrivateMask),
		PublicR:          frontend.Variable(publicR),
		PublicProd:       publicProd,
		PublicCommitment: frontend.Variable(c.PublicCom),
		PrivateSalt:      frontend.Variable(c.PrivateSalt),
	}

	return assignment
}

func GenProofGroth16(assignment HistogramCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment HistogramCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func HistogramGroth16() {
	DummyVecLength = uint64(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// define a dummy vote circuit
	var circuit = HistogramCircuit{
		PrivateX:         make([]frontend.Variable, PrivateItemNum),
		PrivateMask:      0,
		PublicR:          0,
		PublicProd:       0,
		PublicCommitment: 0,
		PrivateSalt:      0,
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)

	// groth16 zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)

	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)
	// Step 1: define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init(rng)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateItemNum)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateItemNum+j] = clients[i].PrivateX[j]
		}
	}

	// shuffled the items
	rand.Shuffle(len(shuffledX), func(i, j int) {
		shuffledX[i], shuffledX[j] = shuffledX[j], shuffledX[i]
	})

	// DETECTION PHASE:

	// Step 1: Client does the following
	// a) randomly sample the dummies (already done when we initialize the clients)
	// b) send the dummies to the shuffler
	// c) send the commitment to the server

	allDummies := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	dummyCnt := 0
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PrivateY); j++ {
			allDummies[dummyCnt] = clients[i].PrivateY[j]
			dummyCnt += 1
		}
	}
	// shuffle the dummies
	rand.Shuffle(len(allDummies), func(i, j int) {
		allDummies[i], allDummies[j] = allDummies[j], allDummies[i]
	})

	commitments := make([]fr_bn254.Element, ClientNum)
	for i := 0; i < ClientNum; i++ {
		commitments[i] = clients[i].PublicCom
	}

	// Step 2: the server broadcasts the publicR
	publicR := randomFr()

	// Step 3:
	// now the clients can compute the assignment
	start = time.Now()
	allAssignment := make([]HistogramCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(publicR)
	}
	prepTime += time.Since(start)

	// now the clients can compute the proofs
	// we only generate proofs for the first MaxNumOfCheckProof clients
	start = time.Now()
	allSubmission := make([]ClientSubmissionToServer, ClientNum)
	for i := 0; i < len(clients); i++ {
		if i < MaxNumOfCheckProof {
			allSubmission[i].proof, allSubmission[i].publicWitness = GenProofGroth16(allAssignment[i], &ccs, &pk)
			allSubmission[i].publicProd = clients[i].PublicProd
		} else {
			allSubmission[i].proof = nil
			allSubmission[i].publicWitness = nil
			allSubmission[i].publicProd = clients[i].PublicProd
		}
	}
	proofTime := time.Since(start)

	// check how many bytes are written per client
	proofSize := 0
	publicWitnessSize := 0
	// proofSize is the size of the allSubmission[0].proof
	// publicWitnessSize is the size of the allSubmission[0].publicWitness
	// we assume that all the proofs and publicWitnesses have the same size
	if allSubmission[0].proof != nil {
		(*(allSubmission[0].proof)).WriteTo(&buf)
		proofSize = buf.Len()
		buf.Reset()
	}
	if allSubmission[0].publicWitness != nil {
		(*(allSubmission[0].publicWitness)).WriteTo(&buf)
		publicWitnessSize = buf.Len()
		buf.Reset()
	}

	// now the server can verify the proofs
	start = time.Now()
	for i := 0; i < len(allSubmission); i++ {
		if i < MaxNumOfCheckProof {
			verification_err := groth16.Verify(*allSubmission[i].proof, vk, *allSubmission[i].publicWitness)
			if verification_err != nil {
				fmt.Printf("verification error in client %v", i)
			}
		}
	}
	verifyTime := time.Since(start)

	// finally, the server verifies the polynomial evaluations
	start = time.Now()

	prodFromShuffler := PolyEval(shuffledX, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}

	// print the product from the shuffler
	fmt.Printf("prodFromShuffler: %v\n", prodFromShuffler)

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < len(clients); i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// now we collect the histogram
	histogram := make([]uint64, UniverseSize)
	for i := 0; i < len(shuffledX); i++ {
		tmp := shuffledX[i].Uint64()
		if tmp >= UniverseSize {
			fmt.Printf("The item is out of the universe\n")
			continue
		}
		histogram[shuffledX[i].Uint64()] += 1
	}
	// find the one with the maximum count
	maxCnt := uint64(0)
	maxIdx := -1
	for i := 0; i < len(histogram); i++ {
		if histogram[i] > maxCnt {
			maxCnt = histogram[i]
			maxIdx = i
		}
	}
	fmt.Printf("The item with the maximum count is %v with %v counts\n", maxIdx, maxCnt)

	//now we compute the cost

	// now we compute the communication
	// the client sends the commitments to the server
	// the server broadcasts the challenge
	// the client sends the public witness and the proof to the server

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Histogram w/ Groth16 Proof)======\n")
	nbConstraints := ccs.GetNbConstraints()
	log.Printf("Number of Constraints: %v\n", nbConstraints)
	log.Printf("============================\n")

	log.Printf("=====Communication Cost (bytes)=====\n")
	log.Printf("Proof: %v\n", proofRelatedCommCost)
	log.Printf("Other: %v\n", commCost-proofRelatedCommCost)
	log.Printf("Total: %v\n", commCost)
	// we now print the breakdown of the communication cost
	log.Printf("Proof Size %v\n", proofSize)
	log.Printf("Public Witness Size %v\n", publicWitnessSize)
	log.Printf("Commitment Size %v\n", CommitmentSize)
	log.Printf("Challenge Size %v\n", BN254Size)
	log.Printf("Dummy Size %v\n", dummyCostPerClient)
	log.Printf("============================\n")

	// now we compute the computation cost
	//23 parts : prep, proof
	clientTime := prepTime/time.Duration(ClientNum) + proofTime/time.Duration(MaxNumOfCheckProof)
	log.Printf("=====Client Computation Cost=====\n")
	log.Printf("Preparation: %v\n", prepTime/time.Duration(ClientNum))
	log.Printf("Proof: %v\n", proofTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", clientTime)
	log.Printf("============================\n")

	// now we compute the server time amortized per client
	serverTotalTime := serverTime/time.Duration(ClientNum) + verifyTime/time.Duration(MaxNumOfCheckProof)
	log.Printf("=====Server Computation Cost=====\n")
	log.Printf("Other: %v\n", serverTime/time.Duration(ClientNum))
	log.Printf("Verify: %v\n", verifyTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", serverTotalTime)
	log.Printf("============================\n")

	// now we compute the storage cost
	// the proving key size is the storage cost
	log.Printf("=====Storage Cost (Bytes) =====\n")
	log.Printf("Proving Key: %v\n", provingKeySize)
	log.Printf("============================\n")

	s := fmt.Sprintf("Histogram Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func HistogramPlonk() {
	DummyVecLength = uint64(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// define a dummy vote circuit
	var circuit = HistogramCircuit{
		PrivateX:         make([]frontend.Variable, PrivateItemNum),
		PrivateMask:      0,
		PublicR:          0,
		PublicProd:       0,
		PublicCommitment: 0,
		PrivateSalt:      0,
	}

	//ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &circuit)
	if err != nil {
		log.Println("scs circuit compile error")
	}

	//setup kzg
	_r1cs := ccs.(*cs.SparseR1CS)
	srs, err := test.NewKZGSRS(_r1cs)
	if err != nil {
		log.Println("kzg srs error")
	}

	// plonk Setup
	pk, vk, _ := plonk.Setup(ccs, srs)
	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)
	// Step 1: define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init(rng)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateItemNum)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateItemNum+j] = clients[i].PrivateX[j]
		}
	}

	// shuffled the items
	rand.Shuffle(len(shuffledX), func(i, j int) {
		shuffledX[i], shuffledX[j] = shuffledX[j], shuffledX[i]
	})

	// DETECTION PHASE:

	// Step 1: Client does the following
	// a) randomly sample the dummies (already done when we initialize the clients)
	// b) send the dummies to the shuffler
	// c) send the commitment to the server

	allDummies := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	dummyCnt := 0
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PrivateY); j++ {
			allDummies[dummyCnt] = clients[i].PrivateY[j]
			dummyCnt += 1
		}
	}
	// shuffle the dummies
	rand.Shuffle(len(allDummies), func(i, j int) {
		allDummies[i], allDummies[j] = allDummies[j], allDummies[i]
	})

	commitments := make([]fr_bn254.Element, ClientNum)
	for i := 0; i < ClientNum; i++ {
		commitments[i] = clients[i].PublicCom
	}

	// Step 2: the server broadcasts the publicR
	publicR := randomFr()

	// Step 3:
	// now the clients can compute the assignment
	start = time.Now()
	allAssignment := make([]HistogramCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(publicR)
	}
	prepTime += time.Since(start)

	// now the clients can compute the proofs
	// we only generate proofs for the first MaxNumOfCheckProof clients
	start = time.Now()
	allSubmission := make([]ClientSubmissionToServerPlonk, ClientNum)
	for i := 0; i < len(clients); i++ {
		if i < MaxNumOfCheckProof {
			allSubmission[i].proof, allSubmission[i].publicWitness = GenProofPlonk(allAssignment[i], &ccs, &pk)
			allSubmission[i].publicProd = clients[i].PublicProd
		} else {
			allSubmission[i].proof = nil
			allSubmission[i].publicWitness = nil
			allSubmission[i].publicProd = clients[i].PublicProd
		}
	}
	proofTime := time.Since(start)

	// check how many bytes are written per client
	proofSize := 0
	publicWitnessSize := 0
	// proofSize is the size of the allSubmission[0].proof
	// publicWitnessSize is the size of the allSubmission[0].publicWitness
	// we assume that all the proofs and publicWitnesses have the same size
	if allSubmission[0].proof != nil {
		(*(allSubmission[0].proof)).WriteTo(&buf)
		proofSize = buf.Len()
		buf.Reset()
	}
	if allSubmission[0].publicWitness != nil {
		(*(allSubmission[0].publicWitness)).WriteTo(&buf)
		publicWitnessSize = buf.Len()
		buf.Reset()
	}

	// now the server can verify the proofs
	start = time.Now()
	for i := 0; i < len(allSubmission); i++ {
		if i < MaxNumOfCheckProof {
			verification_err := plonk.Verify(*allSubmission[i].proof, vk, *allSubmission[i].publicWitness)
			if verification_err != nil {
				fmt.Printf("verification error in client %v", i)
			}
		}
	}
	verifyTime := time.Since(start)

	// finally, the server verifies the polynomial evaluations
	start = time.Now()

	prodFromShuffler := PolyEval(shuffledX, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}

	// print the product from the shuffler
	fmt.Printf("prodFromShuffler: %v\n", prodFromShuffler)

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < len(clients); i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// now we collect the histogram
	histogram := make([]uint64, UniverseSize)
	for i := 0; i < len(shuffledX); i++ {
		tmp := shuffledX[i].Uint64()
		if tmp >= UniverseSize {
			fmt.Printf("The item is out of the universe\n")
			continue
		}
		histogram[shuffledX[i].Uint64()] += 1
	}
	// find the one with the maximum count
	maxCnt := uint64(0)
	maxIdx := -1
	for i := 0; i < len(histogram); i++ {
		if histogram[i] > maxCnt {
			maxCnt = histogram[i]
			maxIdx = i
		}
	}
	fmt.Printf("The item with the maximum count is %v with %v counts\n", maxIdx, maxCnt)

	//now we compute the cost

	// now we compute the communication
	// the client sends the commitments to the server
	// the server broadcasts the challenge
	// the client sends the public witness and the proof to the server

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Histogram w/ Plonk Proof)======\n")
	nbConstraints := ccs.GetNbConstraints()
	log.Printf("Number of Constraints: %v\n", nbConstraints)
	log.Printf("============================\n")

	log.Printf("=====Communication Cost (bytes)=====\n")
	log.Printf("Proof: %v\n", proofRelatedCommCost)
	log.Printf("Other: %v\n", commCost-proofRelatedCommCost)
	log.Printf("Total: %v\n", commCost)
	// we now print the breakdown of the communication cost
	log.Printf("Proof Size %v\n", proofSize)
	log.Printf("Public Witness Size %v\n", publicWitnessSize)
	log.Printf("Commitment Size %v\n", CommitmentSize)
	log.Printf("Challenge Size %v\n", BN254Size)
	log.Printf("Dummy Size %v\n", dummyCostPerClient)
	log.Printf("============================\n")

	// now we compute the computation cost
	//23 parts : prep, proof
	clientTime := prepTime/time.Duration(ClientNum) + proofTime/time.Duration(MaxNumOfCheckProof)
	log.Printf("=====Client Computation Cost=====\n")
	log.Printf("Preparation: %v\n", prepTime/time.Duration(ClientNum))
	log.Printf("Proof: %v\n", proofTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", clientTime)
	log.Printf("============================\n")

	// now we compute the server time amortized per client
	serverTotalTime := serverTime/time.Duration(ClientNum) + verifyTime/time.Duration(MaxNumOfCheckProof)
	log.Printf("=====Server Computation Cost=====\n")
	log.Printf("Other: %v\n", serverTime/time.Duration(ClientNum))
	log.Printf("Verify: %v\n", verifyTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", serverTotalTime)
	log.Printf("============================\n")

	// now we compute the storage cost
	// the proving key size is the storage cost
	log.Printf("=====Storage Cost (Bytes) =====\n")
	log.Printf("Proving Key: %v\n", provingKeySize)
	log.Printf("============================\n")

	s := fmt.Sprintf("Histogram Plonk, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func main() {
	var err error
	file, err = os.OpenFile("output-histogram.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		HistogramGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		HistogramPlonk()
	}

	//ShuffleZKPlonk()
}
