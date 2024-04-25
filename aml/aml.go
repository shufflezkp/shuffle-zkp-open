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
	PrivateTxNum       = 200
	PublicThreshold    = 10000
	MaxNumOfCheckProof = 10
	ClientNum          = 1000
	CorruptedNum       = 500
	e                  = 2.71828182845904523536028747135266249775724709369995
	BN254Size          = 32
	CommitmentSize     = 32
	TestRepeat         = 5
	BlacklistSize      = 50
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

type PrivateTx struct {
	Send    fr_bn254.Element
	Recv    fr_bn254.Element
	Amt     fr_bn254.Element
	Tx_salt fr_bn254.Element
}

type PrivateTxVar struct {
	Send    frontend.Variable
	Recv    frontend.Variable
	Amt     frontend.Variable
	Tx_salt frontend.Variable
}

type AMLCircuit struct {
	PrivateTxs  []PrivateTxVar
	PrivateHash []frontend.Variable
	/*
		PrivateSender []frontend.Variable
		PrivateRecv   []frontend.Variable
		PrivateAmt    []frontend.Variable
		PrivateTxSalt []frontend.Variable
		PrivateHash   []frontend.Variable
	*/

	PublicThreshold frontend.Variable   `gnark:",public"`
	PublicBlacklist []frontend.Variable `gnark:",public"`

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *AMLCircuit) Define(api frontend.API) error {
	//First check that each tx corresponds to a valid hash
	for i := 0; i < len(circuit.PrivateTxs); i++ {
		mimc, _ := mimc.NewMiMC(api)
		mimc.Write(circuit.PrivateTxs[i].Send)
		mimc.Write(circuit.PrivateTxs[i].Recv)
		mimc.Write(circuit.PrivateTxs[i].Amt)
		mimc.Write(circuit.PrivateTxs[i].Tx_salt)
		api.AssertIsEqual(circuit.PrivateHash[i], mimc.Sum())
	}

	// Then, for each recv address, check that the sum of the amt to that address is less than the threshold
	for i := 0; i < len(circuit.PrivateTxs); i++ {
		current_addr := circuit.PrivateTxs[i].Recv
		current_amount := frontend.Variable(0)
		for j := 0; j < len(circuit.PrivateTxs); j++ {
			diff := api.Sub(current_addr, circuit.PrivateTxs[j].Recv)
			diff_is_zero := api.IsZero(diff)
			current_amount = api.Add(current_amount, api.Mul(diff_is_zero, circuit.PrivateTxs[j].Amt))
		}
		api.AssertIsLessOrEqual(current_amount, circuit.PublicThreshold)
	}

	// For each recv address, check that they are not equal to the blacklist
	// we do it by multiplying the difference of the current address with each address in the blacklist
	tmp := frontend.Variable(1)
	for i := 0; i < len(circuit.PrivateTxs); i++ {
		current_addr := circuit.PrivateTxs[i].Recv
		for j := 0; j < len(circuit.PublicBlacklist); j++ {
			diff := api.Sub(current_addr, circuit.PublicBlacklist[j])
			tmp = api.Mul(tmp, diff)
		}
	}

	api.AssertIsDifferent(tmp, frontend.Variable(0))

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, circuit.PrivateHash, circuit.PublicR)
	privateProd = api.Mul(privateProd, circuit.PrivateMask)
	//privateProd = api.Mul(privateProd, PolyEvalInCircuit(api, circuit.DummyVec, circuit.PublicR))
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	// Check commitment for the private hashes and the private mask w/ the salt
	mimc, _ := mimc.NewMiMC(api)
	for i := 0; i < len(circuit.PrivateHash); i++ {
		mimc.Write(circuit.PrivateHash[i])
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
//	PrivateVec [PrivateVecLength]fr_bn254.Element
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
	PrivateTxs []PrivateTx        // the private txxs
	PrivateX   []fr_bn254.Element // the private hashes
	PrivateY   []fr_bn254.Element // the private Y are the dummies

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element

	PublicProd fr_bn254.Element
	PublicR    fr_bn254.Element
}

func (c *ClientState) Init(idx int, rng *rand.Rand) {
	c.PrivateTxs = make([]PrivateTx, PrivateTxNum)
	c.PrivateX = make([]fr_bn254.Element, PrivateTxNum)
	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)

	for i := 0; i < PrivateTxNum; i++ {
		send := idx
		recv := rng.Intn(ClientNum)
		amt := rng.Intn(100)

		c.PrivateTxs[i].Send = fr_bn254.NewElement(uint64(send))
		c.PrivateTxs[i].Recv = fr_bn254.NewElement(uint64(recv))
		c.PrivateTxs[i].Amt = fr_bn254.NewElement(uint64(amt))
		c.PrivateTxs[i].Tx_salt = randomFr()

		// mimc hash and store the hash
		goMimc := hash.MIMC_BN254.New()
		tmpBytes := c.PrivateTxs[i].Send.Bytes()
		goMimc.Write(tmpBytes[:])
		tmpBytes = c.PrivateTxs[i].Recv.Bytes()
		goMimc.Write(tmpBytes[:])
		tmpBytes = c.PrivateTxs[i].Amt.Bytes()
		goMimc.Write(tmpBytes[:])
		tmpBytes = c.PrivateTxs[i].Tx_salt.Bytes()
		goMimc.Write(tmpBytes[:])

		c.PrivateX[i].SetBytes(goMimc.Sum(nil))
	}

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

func (c *ClientState) GenAssignment(publicR fr_bn254.Element, blacklist []int) AMLCircuit {
	// first initialize all the variables in the circuit
	PrivateTxVars := make([]PrivateTxVar, len(c.PrivateTxs))
	PrivateHashVars := make([]frontend.Variable, len(c.PrivateX))
	PublicBlacklist := make([]frontend.Variable, len(blacklist))
	for i := 0; i < len(c.PrivateTxs); i++ {
		PrivateTxVars[i].Send = frontend.Variable(c.PrivateTxs[i].Send)
		PrivateTxVars[i].Recv = frontend.Variable(c.PrivateTxs[i].Recv)
		PrivateTxVars[i].Amt = frontend.Variable(c.PrivateTxs[i].Amt)
		PrivateTxVars[i].Tx_salt = frontend.Variable(c.PrivateTxs[i].Tx_salt)
		PrivateHashVars[i] = frontend.Variable(c.PrivateX[i])
	}

	for i := 0; i < len(blacklist); i++ {
		PublicBlacklist[i] = frontend.Variable(fr_bn254.NewElement(uint64(blacklist[i])))
	}

	c.ComputePolyEval(publicR)
	publicProd := frontend.Variable(c.PublicProd)

	// now we create the assignment
	assignment := AMLCircuit{
		PrivateTxs:       PrivateTxVars[:],
		PrivateHash:      PrivateHashVars[:],
		PublicThreshold:  frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		PublicBlacklist:  PublicBlacklist[:],
		PrivateMask:      frontend.Variable(c.PrivateMask),
		PublicR:          frontend.Variable(publicR),
		PublicProd:       publicProd,
		PublicCommitment: frontend.Variable(c.PublicCom),
		PrivateSalt:      frontend.Variable(c.PrivateSalt),
	}

	return assignment
}

func GenProofGroth16(assignment AMLCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment AMLCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func AMLGroth16() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	//initialize a dummy circuit

	dummyPrivateTxsVar := make([]PrivateTxVar, PrivateTxNum)
	dummyPrivateHashVar := make([]frontend.Variable, PrivateTxNum)
	dummyBlacklist := make([]frontend.Variable, BlacklistSize)

	for i := 0; i < PrivateTxNum; i++ {
		dummyPrivateTxsVar[i] = PrivateTxVar{
			Send:    frontend.Variable(0),
			Recv:    frontend.Variable(0),
			Amt:     frontend.Variable(0),
			Tx_salt: frontend.Variable(0),
		}
		dummyPrivateHashVar[i] = frontend.Variable(0)
	}

	for i := 0; i < BlacklistSize; i++ {
		dummyBlacklist[i] = frontend.Variable(0)
	}

	var circuit = AMLCircuit{
		PrivateTxs:       dummyPrivateTxsVar[:],
		PrivateHash:      dummyPrivateHashVar[:],
		PublicThreshold:  0,
		PublicBlacklist:  dummyBlacklist[:],
		PrivateMask:      0,
		PublicR:          0,
		PublicProd:       0,
		PublicCommitment: 0,
		PrivateSalt:      0,
	}

	//ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)

	// groth16 zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)
	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// generate a list of banned clients
	blacklist := make([]int, BlacklistSize)
	for i := 0; i < BlacklistSize; i++ {
		blacklist[i] = i + 9999 // just make a number that is not in the range of [0, ClientNum)
	}

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)

	// we now set up the clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < ClientNum; i++ {
		clients[i].Init(i, rng)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits the hash of their txs to the shuffler
	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateTxNum)
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateTxNum+j] = clients[i].PrivateX[j]
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
	allAssignment := make([]AMLCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(publicR, blacklist)
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

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (AML w/ Groth16 Proof)======\n")
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

	s := fmt.Sprintf("AML Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func AMLPlonk() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	//initialize a dummy circuit

	dummyPrivateTxsVar := make([]PrivateTxVar, PrivateTxNum)
	dummyPrivateHashVar := make([]frontend.Variable, PrivateTxNum)
	dummyBlacklist := make([]frontend.Variable, BlacklistSize)

	for i := 0; i < PrivateTxNum; i++ {
		dummyPrivateTxsVar[i] = PrivateTxVar{
			Send:    frontend.Variable(0),
			Recv:    frontend.Variable(0),
			Amt:     frontend.Variable(0),
			Tx_salt: frontend.Variable(0),
		}
		dummyPrivateHashVar[i] = frontend.Variable(0)
	}

	for i := 0; i < BlacklistSize; i++ {
		dummyBlacklist[i] = frontend.Variable(0)
	}

	var circuit = AMLCircuit{
		PrivateTxs:       dummyPrivateTxsVar[:],
		PrivateHash:      dummyPrivateHashVar[:],
		PublicThreshold:  0,
		PublicBlacklist:  dummyBlacklist[:],
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

	// generate a list of banned clients
	blacklist := make([]int, BlacklistSize)
	for i := 0; i < BlacklistSize; i++ {
		blacklist[i] = i + 9999 // just make a number that is not in the range of [0, ClientNum)
	}

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)

	// we now set up the clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < ClientNum; i++ {
		clients[i].Init(i, rng)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits the hash of their txs to the shuffler
	shuffledX := make([]fr_bn254.Element, ClientNum*PrivateTxNum)
	for i := 0; i < ClientNum; i++ {
		for j := 0; j < len(clients[i].PrivateX); j++ {
			shuffledX[i*PrivateTxNum+j] = clients[i].PrivateX[j]
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
	allAssignment := make([]AMLCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(publicR, blacklist)
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

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (AML w/ Plonk Proof)======\n")
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

	s := fmt.Sprintf("AML Plonk, %v, %v, %v, %v, %v, %v, %v\n",
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
	file, err = os.OpenFile("output-aml.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		AMLGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		AMLPlonk()
	}
}
