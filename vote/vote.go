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
	PrivateShareNum = 60
	CandidateNum    = 10
	//DummyVecLength   = 60
	ClientNum          = 1000
	CorruptedNum       = 500
	e                  = 2.71828182845904523536028747135266249775724709369995
	BN254Size          = 32
	CommitmentSize     = 32
	MaxNumOfCheckProof = 10
	TestRepeat         = 1
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

type VoteCircuit struct {
	//UnsortedCandidate []frontend.Variable `gnark:",public"`
	// sorted candidate list. Should be a permutation of 0 - (CandidateNum - 1)
	SortedCandidate []frontend.Variable

	// (c * (c - 1) / 2) comparison pairs.
	// A pair (Alice Bob) means Alice is ranked higher than Bob
	PairFirstVar  []frontend.Variable
	PairSecondVar []frontend.Variable

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *VoteCircuit) Define(api frontend.API) error {

	// first verify that the unsorted candidate list is a permutation of 0 - (CandidateNum - 1)
	unsortedCandidate := make([]frontend.Variable, CandidateNum)
	for i := 0; i < CandidateNum; i++ {
		//api.AssertIsEqual(circuit.UnsortedCandidate[i], frontend.Variable(i))
		unsortedCandidate[i] = frontend.Variable(i)
	}

	// then verify that the sorted candidate list is a permutation of 0 - (CandidateNum - 1)
	unsortedProd := PolyEvalInCircuit(api, unsortedCandidate, circuit.PublicR)
	sortedProd := PolyEvalInCircuit(api, circuit.SortedCandidate, circuit.PublicR)
	api.AssertIsEqual(unsortedProd, sortedProd)

	// Then verify that the pairs are correct
	// Essentially, there are (c * (c - 1) / 2) pairs
	// It should be arranged in the following way:
	// Let's say the rankings are [1, 0, 2, 3]
	// Then there are 4 rows, and the pairs are:
	// (1, 0), (1, 2), (1, 3)
	// (0, 2), (0, 3)
	// (2, 3)

	processedVec := make([]frontend.Variable, len(circuit.PairFirstVar))
	base := 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			// first verify the first element of the pair is sorted[i]
			api.AssertIsEqual(circuit.PairFirstVar[base+j], circuit.SortedCandidate[i])

			// then verify the second element of the pair is sorted[i+j+1]
			api.AssertIsEqual(circuit.PairSecondVar[base+j], circuit.SortedCandidate[i+j+1])

			// the processedVec should be first * CandidateNum + second
			processedVec[base+j] = api.Add(api.Mul(circuit.PairFirstVar[base+j], frontend.Variable(CandidateNum)), circuit.PairSecondVar[base+j])
		}
		base += CandidateNum - i - 1
	}

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, processedVec, circuit.PublicR)
	privateProd = api.Mul(privateProd, circuit.PrivateMask)
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	// checking commitment
	mimc, _ := mimc.NewMiMC(api)
	for i := 0; i < len(circuit.PairFirstVar); i++ {
		mimc.Write(processedVec[i])
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
	SortedCandidate []fr_bn254.Element
	PairFirst       []fr_bn254.Element
	PairSecond      []fr_bn254.Element

	PrivateX []fr_bn254.Element // the private X are the packed version of the pairs
	PrivateY []fr_bn254.Element // the private Y are the dummies

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element

	PublicProd fr_bn254.Element
	PublicR    fr_bn254.Element
}

func (c *ClientState) Init() {
	c.SortedCandidate = make([]fr_bn254.Element, CandidateNum)
	c.PairFirst = make([]fr_bn254.Element, CandidateNum*(CandidateNum-1)/2)
	c.PairSecond = make([]fr_bn254.Element, CandidateNum*(CandidateNum-1)/2)
	c.PrivateX = make([]fr_bn254.Element, CandidateNum*(CandidateNum-1)/2)
	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)

	for i := 0; i < CandidateNum; i++ {
		c.SortedCandidate[i] = fr_bn254.NewElement(uint64(i))
	}

	//create a random order of the candidate
	rand.Shuffle(len(c.SortedCandidate), func(i, j int) {
		c.SortedCandidate[i], c.SortedCandidate[j] = c.SortedCandidate[j], c.SortedCandidate[i]
	})

	currentPair := 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			p, q := c.SortedCandidate[i], c.SortedCandidate[i+j+1]
			c.PairFirst[currentPair] = p
			c.PairSecond[currentPair] = q
			currentPair += 1
		}
	}

	for i := 0; i < len(c.PrivateX); i++ {
		tmp := fr_bn254.NewElement(uint64(CandidateNum))
		tmp.Mul(&tmp, &c.PairFirst[i])
		tmp.Add(&tmp, &c.PairSecond[i])
		c.PrivateX[i] = tmp
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

func (c *ClientState) GenAssignment(publicR fr_bn254.Element) VoteCircuit {
	// first initialize all variables needed in the votecircuit
	unsortedCandidate := make([]frontend.Variable, CandidateNum)
	sortedCandidate := make([]frontend.Variable, CandidateNum)
	pairFirstVar := make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2)
	pairSecondVar := make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2)

	for i := 0; i < CandidateNum; i++ {
		unsortedCandidate[i] = frontend.Variable(i)
		sortedCandidate[i] = frontend.Variable(c.SortedCandidate[i])
	}

	for i := 0; i < len(pairFirstVar); i++ {
		pairFirstVar[i] = frontend.Variable(c.PairFirst[i])
		pairSecondVar[i] = frontend.Variable(c.PairSecond[i])
	}

	// now compute the public prod
	c.ComputePolyEval(publicR)
	publicProd := frontend.Variable(c.PublicProd)

	// now create the assignment
	assignment := VoteCircuit{
		SortedCandidate:  sortedCandidate,
		PairFirstVar:     pairFirstVar,
		PairSecondVar:    pairSecondVar,
		PrivateMask:      frontend.Variable(c.PrivateMask),
		PublicR:          frontend.Variable(publicR),
		PublicProd:       publicProd,
		PublicCommitment: frontend.Variable(c.PublicCom),
		PrivateSalt:      frontend.Variable(c.PrivateSalt),
	}

	return assignment
}

func GenProofGroth16(assignment VoteCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment VoteCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func VoteGroth16() {
	DummyVecLength = uint64(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// define a dummy vote circuit
	var circuit = VoteCircuit{
		SortedCandidate:  make([]frontend.Variable, CandidateNum),
		PairFirstVar:     make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2),
		PairSecondVar:    make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2),
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

	// Step 1: define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init()
	}
	prepTime := time.Since(start)

	// print the information of the 0-th client
	fmt.Printf("=====Client 0=====\n")
	for i := 0; i < len(clients[0].SortedCandidate); i++ {
		// print the sorted candidate, cast it to uint64
		fmt.Printf("rank: %v", clients[0].SortedCandidate[i].Uint64())
	}
	fmt.Printf("\n")
	tmpCnt := 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			fmt.Printf("(%v, %v)", clients[0].PairFirst[tmpCnt].Uint64(), clients[0].PairSecond[tmpCnt].Uint64())
			tmpCnt += 1
		}
		fmt.Printf("\n")
	}
	tmpCnt = 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			fmt.Printf("%v ", clients[0].PrivateX[tmpCnt].Uint64())
			tmpCnt += 1
		}
		fmt.Printf("\n")
	}
	fmt.Printf("============================\n")

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	shuffledPairFirst := make([]fr_bn254.Element, ClientNum*(CandidateNum*(CandidateNum-1)/2))
	shuffledPairSecond := make([]fr_bn254.Element, ClientNum*(CandidateNum*(CandidateNum-1)/2))

	voteCnt := 0
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PairFirst); j++ {
			shuffledPairFirst[voteCnt] = clients[i].PairFirst[j]
			shuffledPairSecond[voteCnt] = clients[i].PairSecond[j]
			voteCnt += 1
		}
	}
	// shuffled the votes. Shuffle the pairFirst and pairSecond with the same permutation
	rand.Shuffle(len(shuffledPairFirst), func(i, j int) {
		shuffledPairFirst[i], shuffledPairFirst[j] = shuffledPairFirst[j], shuffledPairFirst[i]
		shuffledPairSecond[i], shuffledPairSecond[j] = shuffledPairSecond[j], shuffledPairSecond[i]
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
	allAssignment := make([]VoteCircuit, ClientNum)
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

	processedVec := make([]fr_bn254.Element, len(shuffledPairFirst))
	for i := 0; i < len(shuffledPairFirst); i++ {
		tmp := fr_bn254.NewElement(uint64(CandidateNum))
		tmp.Mul(&tmp, &shuffledPairFirst[i])
		tmp.Add(&tmp, &shuffledPairSecond[i])
		processedVec[i] = tmp
	}
	prodFromShuffler := PolyEval(processedVec, publicR)
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

	// now we see if there is any sole winner
	comparisonVoteCnt := make([][]uint64, CandidateNum)
	for i := 0; i < len(comparisonVoteCnt); i++ {
		comparisonVoteCnt[i] = make([]uint64, CandidateNum)
	}
	for i := 0; i < len(shuffledPairFirst); i++ {
		comparisonVoteCnt[shuffledPairFirst[i].Uint64()][shuffledPairSecond[i].Uint64()] += 1
	}
	soleWinner := -1
	for i := 0; i < CandidateNum; i++ {
		ok := true
		for j := 0; j < CandidateNum; j++ {
			if i != j && comparisonVoteCnt[i][j] <= comparisonVoteCnt[j][i] {
				ok = false
				break
			}
			if i != j && comparisonVoteCnt[i][j]+comparisonVoteCnt[j][i] != ClientNum {
				fmt.Print("The comparison is not correct\n")
			}
		}
		if ok {
			fmt.Printf("The sole winner is %v\n", i)
			// print the vote for the sole winner
			for j := 0; j < CandidateNum; j++ {
				fmt.Printf("%v ", comparisonVoteCnt[i][j])
			}
			soleWinner = i
		}
	}
	if soleWinner == -1 {
		fmt.Printf("There is no sole winner\n")
	}

	//now we compute the cost

	// now we compute the communication
	// the client sends the commitments to the server
	// the server broadcasts the challenge
	// the client sends the public witness and the proof to the server

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Voting w/ Groth16 Proof)======\n")
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

	s := fmt.Sprintf("Voting Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func VotePlonk() {
	DummyVecLength = uint64(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// define a dummy vote circuit
	var circuit = VoteCircuit{
		SortedCandidate:  make([]frontend.Variable, CandidateNum),
		PairFirstVar:     make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2),
		PairSecondVar:    make([]frontend.Variable, CandidateNum*(CandidateNum-1)/2),
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

	// Step 1: define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init()
	}
	prepTime := time.Since(start)

	// print the information of the 0-th client
	fmt.Printf("=====Client 0=====\n")
	for i := 0; i < len(clients[0].SortedCandidate); i++ {
		// print the sorted candidate, cast it to uint64
		fmt.Printf("rank: %v", clients[0].SortedCandidate[i].Uint64())
	}
	fmt.Printf("\n")
	tmpCnt := 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			fmt.Printf("(%v, %v)", clients[0].PairFirst[tmpCnt].Uint64(), clients[0].PairSecond[tmpCnt].Uint64())
			tmpCnt += 1
		}
		fmt.Printf("\n")
	}
	tmpCnt = 0
	for i := 0; i < CandidateNum; i++ {
		for j := 0; j < CandidateNum-i-1; j++ {
			fmt.Printf("%v ", clients[0].PrivateX[tmpCnt].Uint64())
			tmpCnt += 1
		}
		fmt.Printf("\n")
	}
	fmt.Printf("============================\n")

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	shuffledPairFirst := make([]fr_bn254.Element, ClientNum*(CandidateNum*(CandidateNum-1)/2))
	shuffledPairSecond := make([]fr_bn254.Element, ClientNum*(CandidateNum*(CandidateNum-1)/2))

	voteCnt := 0
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].PairFirst); j++ {
			shuffledPairFirst[voteCnt] = clients[i].PairFirst[j]
			shuffledPairSecond[voteCnt] = clients[i].PairSecond[j]
			voteCnt += 1
		}
	}
	// shuffled the votes. Shuffle the pairFirst and pairSecond with the same permutation
	rand.Shuffle(len(shuffledPairFirst), func(i, j int) {
		shuffledPairFirst[i], shuffledPairFirst[j] = shuffledPairFirst[j], shuffledPairFirst[i]
		shuffledPairSecond[i], shuffledPairSecond[j] = shuffledPairSecond[j], shuffledPairSecond[i]
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
	allAssignment := make([]VoteCircuit, ClientNum)
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

	processedVec := make([]fr_bn254.Element, len(shuffledPairFirst))
	for i := 0; i < len(shuffledPairFirst); i++ {
		tmp := fr_bn254.NewElement(uint64(CandidateNum))
		tmp.Mul(&tmp, &shuffledPairFirst[i])
		tmp.Add(&tmp, &shuffledPairSecond[i])
		processedVec[i] = tmp
	}
	prodFromShuffler := PolyEval(processedVec, publicR)
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

	// now we see if there is any sole winner
	comparisonVoteCnt := make([][]uint64, CandidateNum)
	for i := 0; i < len(comparisonVoteCnt); i++ {
		comparisonVoteCnt[i] = make([]uint64, CandidateNum)
	}
	for i := 0; i < len(shuffledPairFirst); i++ {
		comparisonVoteCnt[shuffledPairFirst[i].Uint64()][shuffledPairSecond[i].Uint64()] += 1
	}
	soleWinner := -1
	for i := 0; i < CandidateNum; i++ {
		ok := true
		for j := 0; j < CandidateNum; j++ {
			if i != j && comparisonVoteCnt[i][j] <= comparisonVoteCnt[j][i] {
				ok = false
				break
			}
			if i != j && comparisonVoteCnt[i][j]+comparisonVoteCnt[j][i] != ClientNum {
				fmt.Print("The comparison is not correct\n")
			}
		}
		if ok {
			fmt.Printf("The sole winner is %v\n", i)
			// print the vote for the sole winner
			for j := 0; j < CandidateNum; j++ {
				fmt.Printf("%v ", comparisonVoteCnt[i][j])
			}
			soleWinner = i
		}
	}
	if soleWinner == -1 {
		fmt.Printf("There is no sole winner\n")
	}

	//now we compute the cost

	// now we compute the communication
	// the client sends the commitments to the server
	// the server broadcasts the challenge
	// the client sends the public witness and the proof to the server

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Voting w/ Plonk)======\n")
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

	s := fmt.Sprintf("Voting Plonk, %v, %v, %v, %v, %v, %v, %v\n",
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
	file, err = os.OpenFile("output-vote.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		VoteGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		VotePlonk()
	}

	//ShuffleZKPlonk()
}
