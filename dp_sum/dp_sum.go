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

	//"gonum.org/v1/gonum/stat/sampleuv"

	cs "github.com/consensys/gnark/constraint/bn254"
)

const (
	PrivateVecLength = 60
	ClientNum        = 1000
	CorruptedNum     = 500
	e                = 2.71828182845904523536028747135266249775724709369995
	BN254Size        = 32
	CommitmentSize   = 32
	eps              = 1.0

	ClientValRange = 1000       // the client's value is between 0 and 1000
	NoiseRange     = 500        // the noise is between -500 and 500
	ConstShift     = NoiseRange // the value is shifted by NoiseRange to make sure it is positive

	// How many actual proofs we want to check
	MaxNumOfCheckProof = 10
	// How many repetitions we want to test
	TestRepeat = 1
)

var DummyVecLength uint64
var file *os.File

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

type SumAndCmpCircuit struct {
	PrivateVec      []frontend.Variable
	PublicThreshold frontend.Variable `gnark:",public"`

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *SumAndCmpCircuit) Define(api frontend.API) error {
	// check 0 <= sum <= threshold
	sum := frontend.Variable(0)
	for i := 0; i < len(circuit.PrivateVec); i++ {
		sum = api.Add(sum, circuit.PrivateVec[i])
	}
	zero := frontend.Variable(0)
	api.AssertIsLessOrEqual(zero, sum)
	api.AssertIsLessOrEqual(sum, circuit.PublicThreshold)

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, circuit.PrivateVec, circuit.PublicR)
	privateProd = api.Mul(privateProd, circuit.PrivateMask)
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	// checking commitment
	mimc, _ := mimc.NewMiMC(api)
	for i := 0; i < len(circuit.PrivateVec); i++ {
		mimc.Write(circuit.PrivateVec[i])
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
	PrivateVal   int                // the private value
	PrivateNoise int                // the private noise
	PrivateX     []fr_bn254.Element // the private X are the shares
	PrivateY     []fr_bn254.Element // the private Y are the dummies

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element

	PublicProd fr_bn254.Element
	PublicR    fr_bn254.Element
}

func (c *ClientState) Init(x int, noise int) {
	c.PrivateVal = x
	c.PrivateNoise = noise
	c.PrivateX = make([]fr_bn254.Element, PrivateVecLength)
	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)

	valueToShare := x + noise + ConstShift // we add big enough shift to make sure the value is positive

	// now we split the value into multiple shares
	remainingVal := fr_bn254.NewElement(uint64(valueToShare))
	for i := 0; i < PrivateVecLength-1; i++ {
		c.PrivateX[i] = randomFr()
		remainingVal.Sub(&remainingVal, &c.PrivateX[i])
	}
	c.PrivateX[PrivateVecLength-1] = remainingVal

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

func (c *ClientState) GenAssignment(publicR fr_bn254.Element) SumAndCmpCircuit {
	// first initialize all the variables in the circuit
	privateVec := make([]frontend.Variable, PrivateVecLength)
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(c.PrivateX[i])
	}

	c.ComputePolyEval(publicR)
	publicProd := frontend.Variable(c.PublicProd)

	// now we create the assignment
	assignment := SumAndCmpCircuit{
		PrivateVec:       privateVec[:],
		PublicThreshold:  frontend.Variable(fr_bn254.NewElement(uint64(ClientValRange + ConstShift))),
		PrivateMask:      frontend.Variable(c.PrivateMask),
		PublicR:          frontend.Variable(publicR),
		PublicProd:       publicProd,
		PublicCommitment: frontend.Variable(c.PublicCom),
		PrivateSalt:      frontend.Variable(c.PrivateSalt),
	}
	return assignment
}

func GenProofGroth16(assignment SumAndCmpCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment SumAndCmpCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func DPSumGroth16() {
	// compute the dummy number needed
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// setup the constraint system
	privateVec := make([]frontend.Variable, PrivateVecLength)
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	var circuit = SumAndCmpCircuit{
		PrivateVec:       privateVec[:],
		PublicThreshold:  0,
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
	provingKeySize := buf.Len()
	buf.Reset()

	// we now setup the client state
	start := time.Now()

	clients := make([]ClientState, ClientNum)
	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)
	for i := 0; i < ClientNum; i++ {
		// here we just give the client a default value of 1000
		// try change it to 2000 and the proof process will fail
		clients[i].Init(1000, noise[i])
	}
	prepTime := time.Since(start)

	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)

	// DATA COLLECTION PHASE: each client submits its private value to the shuffler
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateVecLength+j] = clients[i].PrivateX[j]
		}
	}
	// shuffle the shuffledX
	rand.Shuffle(len(shuffledX), func(i, j int) {
		shuffledX[i], shuffledX[j] = shuffledX[j], shuffledX[i]
	})

	// DETECTION PHASE:

	// Step 1: Client does the following
	// a) randomly sample the dummies (already done when we initialize the clients)
	// b) send the dummies to the shuffler
	// c) send the commitment to the server

	allDummies := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateY); j++ {
			allDummies[i*int(DummyVecLength)+j] = clients[i].PrivateY[j]
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
	allAssignment := make([]SumAndCmpCircuit, ClientNum)
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

	// Step 4:
	// a) The server verfies all the proofs
	// b) The server checks the polynomial evaluations
	// c) The server computes the sum of all the secret values

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

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < ClientNum; i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	prodFromShuffler := PolyEval(shuffledX, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}
	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// the server then computes the sum of all the secret values
	sum := fr_bn254.NewElement(uint64(0))
	for i := 0; i < len(shuffledX); i++ {
		sum.Add(&sum, &shuffledX[i])
	}

	fmt.Printf("The computed sum is %v\n", sum.Uint64())

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (DP Sum w/ Groth16 Proof)======\n")
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

	s := fmt.Sprintf("DP Sum Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func DPSumPlonk() {
	// compute the dummy number needed
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// setup the constraint system
	privateVec := make([]frontend.Variable, PrivateVecLength)
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	var circuit = SumAndCmpCircuit{
		PrivateVec:       privateVec[:],
		PublicThreshold:  0,
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

	// plonk zkSNARK: Setup
	pk, vk, _ := plonk.Setup(ccs, srs)
	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// we now setup the client state
	start := time.Now()

	clients := make([]ClientState, ClientNum)
	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)
	for i := 0; i < ClientNum; i++ {
		// here we just give the client a default value of 1000
		// try change it to 2000 and the proof process will fail
		clients[i].Init(1000, noise[i])
	}
	prepTime := time.Since(start)

	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)

	// DATA COLLECTION PHASE: each client submits its private value to the shuffler
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateVecLength+j] = clients[i].PrivateX[j]
		}
	}
	// shuffle the shuffledX
	rand.Shuffle(len(shuffledX), func(i, j int) {
		shuffledX[i], shuffledX[j] = shuffledX[j], shuffledX[i]
	})

	// DETECTION PHASE:

	// Step 1: Client does the following
	// a) randomly sample the dummies (already done when we initialize the clients)
	// b) send the dummies to the shuffler
	// c) send the commitment to the server

	allDummies := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateY); j++ {
			allDummies[i*int(DummyVecLength)+j] = clients[i].PrivateY[j]
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
	allAssignment := make([]SumAndCmpCircuit, ClientNum)
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

	// Step 4:
	// a) The server verfies all the proofs
	// b) The server checks the polynomial evaluations
	// c) The server computes the sum of all the secret values

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

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < ClientNum; i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	prodFromShuffler := PolyEval(shuffledX, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}
	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// the server then computes the sum of all the secret values
	sum := fr_bn254.NewElement(uint64(0))
	for i := 0; i < len(shuffledX); i++ {
		sum.Add(&sum, &shuffledX[i])
	}

	fmt.Printf("The computed sum is %v\n", sum.Uint64())

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (DP Sum w/ Plonk Proof)======\n")
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

	s := fmt.Sprintf("DP Sum Plonk, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func GenPolyaPDF(r float64, p float64) []float64 {
	// Generate the PDF for distribution Polya(r, p) for k= 0...99
	fmt.Printf("%v %v\n", r, p)
	ptor := math.Pow(p, r)
	t := 1.0
	accu := math.Gamma(r) // accu_k = gamma(k + r) / k!
	prob := 1.0           // the remaining probability
	pdf := make([]float64, NoiseRange)

	for k := 0; k < len(pdf); k++ {
		density := accu / math.Gamma(r) * t * ptor
		prob = prob - density
		pdf[k] = density
		//fmt.Printf("%v %v\n", k, density)
		t = t * (1 - p)
		accu = accu * (float64(k) + r) / (float64(k) + 1.0)
	}

	fmt.Printf("reamining prob: %v\n", prob)
	pdf[len(pdf)-1] += prob // truncate it at 99, move the remaining prob to 0

	return pdf
}

type DistributionWithPDF struct {
	pdf []float64
	src *rand.Rand
}

func (w DistributionWithPDF) Sample() int {
	// sample a random variable according to the pdf stored in w.pdf
	randNum := w.src.Float64()
	accu := 0.0
	for i := 0; i < len(w.pdf); i++ {
		accu += w.pdf[i]
		if accu >= randNum {
			return i
		}
	}
	return 0
}

func GenDistributedDPNoise(eps float64, sensitivity float64, n int) []int {
	// the pdf shows the PDF for Polya(1/n, e^{-eps/sensitivity}) of k=0...99
	pdf := GenPolyaPDF(1.0/float64(n), 1-math.Exp(-eps/sensitivity))
	//fmt.Printf("%v\n", pdf)

	w := DistributionWithPDF{pdf: pdf, src: rand.New(rand.NewSource(time.Now().UnixNano()))}

	// create the return slice of length n
	noise := make([]int, n)
	sum := 0

	for i := 0; i < n; i++ {
		// sample a random variable between 0 to 99 according to the probability densities stored in pdf
		p1 := w.Sample()
		p2 := w.Sample()
		//fmt.Printf("%v %v\n", p1, p2)
		noise[i] = p1 - p2
		sum += noise[i]
	}

	fmt.Printf("noise sum: %v\n", sum)
	return noise
}

func main() {
	var err error
	file, err = os.OpenFile("output-shuffle-dp-sum.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		DPSumGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		DPSumPlonk()
	}
}
