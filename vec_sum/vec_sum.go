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
	PrivateShareNum  = 60
	PrivateVecLength = 50
	//DummyVecLength   = 60
	PublicThreshold    = 2000
	ClientNum          = 1000
	CorruptedNum       = 500
	e                  = 2.71828182845904523536028747135266249775724709369995
	BN254Size          = 32
	CommitmentSize     = 32
	MaxNumOfCheckProof = 5
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

type VecSumCircuit struct {
	PrivateVec      []frontend.Variable // total length = PrivateShareNum * PrivateVecLength, (( shares of pos 0), (shares of pos 1) ... (shares of pos PrivateVecLength-1))
	PublicThreshold frontend.Variable   `gnark:",public"`

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *VecSumCircuit) Define(api frontend.API) error {
	//assert error if privateVec is empty

	//sum := circuit.PrivateVec[0]
	vecLength := frontend.Variable(PrivateVecLength)
	sum := frontend.Variable(0)
	//fmt.Printf("circuit.PrivateVec: %v\n", circuit.PrivateVec)

	processedVec := make([]frontend.Variable, PrivateVecLength*PrivateShareNum)

	for i := 0; i < PrivateVecLength; i++ {
		realVal := frontend.Variable(0)
		for j := i * PrivateShareNum; j < (i+1)*PrivateShareNum; j++ {
			realVal = api.Add(realVal, circuit.PrivateVec[j])
			processedVec[j] = api.Add(api.Mul(circuit.PrivateVec[j], vecLength), frontend.Variable(i))
			// if the message is (val, i), then we let the processedVec[j] = val * vecLength + i, which is unique
		}
		sum = api.Add(sum, api.Mul(realVal, realVal)) // sum = sum + realVal * realVl
	}

	api.AssertIsLessOrEqual(sum, circuit.PublicThreshold) // compare the L2^2 with the public threshold

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, processedVec, circuit.PublicR)
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
	PrivateVec []int                // the private vector
	PrivateX   [][]fr_bn254.Element // the private X are the shares (of size PrivateShareNum * PrivateVecLength)
	PrivateY   []fr_bn254.Element   // the private Y are the dummies

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element

	PublicProd fr_bn254.Element
	PublicR    fr_bn254.Element
}

func (c *ClientState) Init(x []int) {
	c.PrivateVec = x
	c.PrivateX = make([][]fr_bn254.Element, PrivateVecLength)
	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)

	// now we split the value into multiple shares
	for i := 0; i < len(c.PrivateVec); i++ {
		c.PrivateX[i] = make([]fr_bn254.Element, PrivateShareNum)
		remainingVal := fr_bn254.NewElement(uint64(x[i]))
		for j := 0; j < PrivateShareNum-1; j++ {
			tmp := randomFr()
			c.PrivateX[i][j] = tmp
			remainingVal.Sub(&remainingVal, &tmp)
		}
		c.PrivateX[i][PrivateShareNum-1] = remainingVal
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
		for j := 0; j < len(c.PrivateX[i]); j++ {
			b := c.PrivateX[i][j].Bytes()
			goMimc.Write(b[:])
		}
	}
	b := c.PrivateMask.Bytes()
	goMimc.Write(b[:])
	b = c.PrivateSalt.Bytes()
	goMimc.Write(b[:])
	c.PublicCom.SetBytes(goMimc.Sum(nil))
}

func (c *ClientState) GenAssignment(publicR fr_bn254.Element) VecSumCircuit {
	// first initialize all the variables in the circuit
	processedVec := make([]fr_bn254.Element, PrivateVecLength*PrivateShareNum)
	privateVecVar := make([]frontend.Variable, PrivateVecLength*PrivateShareNum)
	for i := 0; i < PrivateVecLength; i++ {
		for j := 0; j < PrivateShareNum; j++ {
			var tmp fr_bn254.Element
			varLen := fr_bn254.NewElement(uint64(PrivateVecLength))
			vari := fr_bn254.NewElement(uint64(i))

			tmp.Set(&c.PrivateX[i][j])
			tmp.Mul(&tmp, &varLen)
			tmp.Add(&tmp, &vari)
			processedVec[i*PrivateShareNum+j] = tmp
			privateVecVar[i*PrivateShareNum+j] = frontend.Variable(c.PrivateX[i][j])
		}
	}

	prod := PolyEval(processedVec[:], publicR)
	prod.Mul(&prod, &c.PrivateMask)
	c.PublicProd = prod

	// now we create the assignment
	assignment := VecSumCircuit{
		PrivateVec:       privateVecVar[:],
		PublicThreshold:  frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		PrivateMask:      frontend.Variable(c.PrivateMask),
		PublicR:          frontend.Variable(publicR),
		PublicProd:       frontend.Variable(c.PublicProd),
		PublicCommitment: frontend.Variable(c.PublicCom),
		PrivateSalt:      frontend.Variable(c.PrivateSalt),
	}
	return assignment
}

func GenProofGroth16(assignment VecSumCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, err := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	if err != nil {
		// print the error
		fmt.Printf("Error in creating the witness: %v\n", err)
	}

	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment VecSumCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func VecSumGroth16() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	//building dummy

	privateVec := make([]frontend.Variable, PrivateShareNum*PrivateVecLength)
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}

	var circuit = VecSumCircuit{
		PrivateVec:       privateVec[:],
		PublicThreshold:  0,
		PrivateMask:      0,
		PublicR:          0,
		PublicProd:       0,
		PublicCommitment: 0,
		PrivateSalt:      0,
	}
	//ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)

	//groth16 zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)

	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// we now set up the clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < ClientNum; i++ {
		// here we just give the client a default value of 1000
		// try change it to 2000 and the proof process will fail

		clientVec := make([]int, PrivateVecLength)
		for j := 0; j < PrivateVecLength; j++ {
			clientVec[j] = 1
		}
		clients[i].Init(clientVec)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	allSecretVal := make([][]fr_bn254.Element, PrivateVecLength)
	for i := 0; i < PrivateVecLength; i++ {
		allSecretVal[i] = make([]fr_bn254.Element, ClientNum*PrivateShareNum)

		for j := 0; j < ClientNum; j++ {
			for k := 0; k < PrivateShareNum; k++ {
				allSecretVal[i][j*PrivateShareNum+k] = clients[j].PrivateX[i][k]
			}
		}

		// shuffle the allSecretVal
		rand.Shuffle(len(allSecretVal[i]), func(a, b int) {
			allSecretVal[i][a], allSecretVal[i][b] = allSecretVal[i][b], allSecretVal[i][a]
		})
	}

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
	allAssignment := make([]VecSumCircuit, ClientNum)
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

	// Step 4: now the server can verify the proofs
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

	processedVec := make([]fr_bn254.Element, PrivateVecLength*PrivateShareNum*ClientNum)
	for i := 0; i < PrivateVecLength; i++ {
		for j := 0; j < len(allSecretVal[i]); j++ {
			varLen := fr_bn254.NewElement(uint64(PrivateVecLength))
			vari := fr_bn254.NewElement(uint64(i))
			var tmp fr_bn254.Element
			tmp.Set(&allSecretVal[i][j])
			tmp.Mul(&tmp, &varLen)
			tmp.Add(&tmp, &vari)
			processedVec[i*len(allSecretVal[i])+j].Set(&tmp)
		}
	}

	prodFromShuffler := PolyEval(processedVec, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}

	// print the product from the shuffler
	//fmt.Printf("prodFromShuffler: %v\n", prodFromShuffler)

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < len(clients); i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// the server then computes the sum of all the secret values
	sumVec := make([]fr_bn254.Element, PrivateVecLength)
	for i := 0; i < PrivateVecLength; i++ {
		tmp := fr_bn254.NewElement(uint64(0))
		sumVec[i].Set(&tmp)
		for j := 0; j < len(allSecretVal[i]); j++ {
			sumVec[i].Add(&sumVec[i], &allSecretVal[i][j])
		}
	}
	fmt.Printf("The computed sum of pos 0 is %v\n", sumVec[0].Uint64())

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Vec Sum w/ Groth16 Proof)======\n")
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

	s := fmt.Sprintf("Vec Sum Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func VecSumPlonk() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	//building dummy

	privateVec := make([]frontend.Variable, PrivateShareNum*PrivateVecLength)
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}

	var circuit = VecSumCircuit{
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

	// plonk Setup
	pk, vk, _ := plonk.Setup(ccs, srs)
	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// we now set up the clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	for i := 0; i < ClientNum; i++ {
		// here we just give the client a default value of 1000
		// try change it to 2000 and the proof process will fail

		clientVec := make([]int, PrivateVecLength)
		for j := 0; j < PrivateVecLength; j++ {
			clientVec[j] = 1
		}
		clients[i].Init(clientVec)
	}
	prepTime := time.Since(start)

	// DATA COLLECTION PHASE: each client submits its votes to the shuffler

	allSecretVal := make([][]fr_bn254.Element, PrivateVecLength)
	for i := 0; i < PrivateVecLength; i++ {
		allSecretVal[i] = make([]fr_bn254.Element, ClientNum*PrivateShareNum)

		for j := 0; j < ClientNum; j++ {
			for k := 0; k < PrivateShareNum; k++ {
				allSecretVal[i][j*PrivateShareNum+k] = clients[j].PrivateX[i][k]
			}
		}

		// shuffle the allSecretVal
		rand.Shuffle(len(allSecretVal[i]), func(a, b int) {
			allSecretVal[i][a], allSecretVal[i][b] = allSecretVal[i][b], allSecretVal[i][a]
		})
	}

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
	allAssignment := make([]VecSumCircuit, ClientNum)
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

	// Step 4: now the server can verify the proofs
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

	processedVec := make([]fr_bn254.Element, PrivateVecLength*PrivateShareNum*ClientNum)
	for i := 0; i < PrivateVecLength; i++ {
		for j := 0; j < len(allSecretVal[i]); j++ {
			varLen := fr_bn254.NewElement(uint64(PrivateVecLength))
			vari := fr_bn254.NewElement(uint64(i))
			var tmp fr_bn254.Element
			tmp.Set(&allSecretVal[i][j])
			tmp.Mul(&tmp, &varLen)
			tmp.Add(&tmp, &vari)
			processedVec[i*len(allSecretVal[i])+j].Set(&tmp)
		}
	}

	prodFromShuffler := PolyEval(processedVec, publicR)
	for i := 0; i < len(allDummies); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allDummies[i])
	}

	// print the product from the shuffler
	//fmt.Printf("prodFromShuffler: %v\n", prodFromShuffler)

	prodFromClient := fr_bn254.NewElement(uint64(1))
	for i := 0; i < len(clients); i++ {
		prodFromClient.Mul(&prodFromClient, &allSubmission[i].publicProd)
	}

	// now the server compares the prodFromShuffler and the prodFromClients
	if !prodFromShuffler.Equal(&prodFromClient) {
		fmt.Printf("The product from the shuffler and the product from the clients are not equal\n")
	}

	serverTime := time.Since(start)

	// the server then computes the sum of all the secret values
	sumVec := make([]fr_bn254.Element, PrivateVecLength)
	for i := 0; i < PrivateVecLength; i++ {
		tmp := fr_bn254.NewElement(uint64(0))
		sumVec[i].Set(&tmp)
		for j := 0; j < len(allSecretVal[i]); j++ {
			sumVec[i].Add(&sumVec[i], &allSecretVal[i][j])
		}
	}
	fmt.Printf("The computed sum of pos 0 is %v\n", sumVec[0].Uint64())

	proofRelatedCommCost := uint64(proofSize) // + publicWitnessSize
	//commCost := (float64(dummyCostPerClient) + float64(proofSize) + float64(publicWitnessSize) + float64(CommitmentSize) + float64(BN254Size)) / 1024
	dummyCostPerClient := DummyVecLength * uint64(BN254Size)
	commCost := uint64(proofSize) + uint64(publicWitnessSize) + BN254Size + CommitmentSize + dummyCostPerClient

	log.Print("========Stats (Vec Sum w/ Plonk Proof)======\n")
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

	s := fmt.Sprintf("Vec Sum Plonk, %v, %v, %v, %v, %v, %v, %v\n",
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
	file, err = os.OpenFile("output-vec-sum.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		VecSumGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		VecSumPlonk()
	}

	//ShuffleZKPlonk()
}
