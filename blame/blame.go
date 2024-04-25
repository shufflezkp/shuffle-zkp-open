package main

import (
	"bytes"
	"fmt"
	"log"
	"math"
	"math/rand"
	"os"
	"time"

	//"os"

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
	//"gonum.org/v1/gonum/stat/sampleuv"
)

const (
	// 5 private inputs
	PrivateInputSize = 5
	PrivateVecLength = 60
	//DummyVecLength   = 60
	ClientNum          = 1000
	CorruptedNum       = 500
	e                  = 2.71828182845904523536028747135266249775724709369995
	BN254Size          = 32
	eps                = 1.0
	MaxNumOfCheckProof = 10
	TestRepeat         = 1

	MerkleTreeHeight = 16 // should be bigger than CLientNum * PrivateVecLength
)

var file *os.File
var DummyVecLength int

func ComputeDummyNum(lambda uint64, n uint64, t uint64) uint64 {
	tmp := float64(2*lambda+254)/float64(math.Log2(float64(n-t))-math.Log2(e)) + 2
	//tmp := 1.0
	//tmp := 10.0
	return uint64(math.Ceil(tmp))
}

func BatchPIRCost(EntryNum int, EntrySize int, BatchSize int) (int, time.Duration, time.Duration) {
	// return commcost, client time , server time

	// for now assume the commcost is just BtchSize * EntrySize
	// the client time is 0s
	// the server time is 0s

	log.Printf("PIR config is EntryNum %v, EntrySize %v, BatchSize %v\n", EntryNum, EntrySize, BatchSize)
	// we consider using applying PBC code to SimplePIR to support batch PIR.

	// the default DB entries are 118000
	// the default DB entry size is 528 bytes
	// the default query number is 118

	// therefore, we consider using 3-way cuckoo hashing
	// we build a 3*118000 cuckoo hash table and divide it into roughly 174 (roughly 118*1.5, as specified in the PIRANA paper) buckets.
	// Then, each bucket contains 3*118000/174=2040 entries. We round it up to 2048 entries.
	// each entry is 528 bytes, which is 4224 bits

	// Therefore, the batch query takes
	// 174 queries to a DB with 2048 entries, each entry is 4224 bits
	// So the total size DB is 174 * 2048 * 4224 bits = 180MB

	// According to the simulation of SimplePIR,
	// each query takes 6KB * 174 = 1044 KB communication cost
	// each query takes 180MB / (8000MB / s) = 0.0225s server time.  Here, the 8000MB / s is the throughput of the server, which we get from the simulation of SimplePIR
	// the client time is around 2ms.

	commCost := 1044 * 1024
	serverTime := time.Duration(22500) * time.Microsecond
	clientTime := time.Duration(2) * time.Millisecond

	return commCost, clientTime, serverTime
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

type BlameCircuit struct {
	// public statements
	PublicCommitment frontend.Variable   `gnark:",public"` // com_i
	MerkleRootX      frontend.Variable   `gnark:",public"` // digest(S_x)
	MerkleRootY      frontend.Variable   `gnark:",public"` // digest (S_y)
	SerialNumX       []frontend.Variable `gnark:",public"` // sx_{i,1} ... sx_{i, m}
	SerialNumY       []frontend.Variable `gnark:",public"` // sy_{i,1} ... sy_{i, d}

	// private inputs
	PrivateSalt frontend.Variable   // gamma_i
	PrivateMask frontend.Variable   // rho_i
	PrivateX    []frontend.Variable // x_{i,1}...x_{i,m}
	CommSrnX    []frontend.Variable // com(sx_{i,1}, beta_{i,1}) ... com(sx_{i,m}, beta_{i,m})
	BetaX       []frontend.Variable // private salts for serial numbers

	// merkle proof for sx_{i,1} ... sx_{i,m}.
	// it will be a m * merkleTreeHeight array
	MerkleProofX []frontend.Variable
	// also need to specify the left or right child. 0 for left and 1 for right
	MerklePositionX []frontend.Variable

	PrivateY []frontend.Variable // y_{i,1}...y_{i,d}
	CommSrnY []frontend.Variable // com(sy_{i,1}, beta'_{i,1}) ... com(sy_{i,d}, beta'_{i,m})
	BetaY    []frontend.Variable // private salts for serial numbers

	// merkle proof for sx_{i,1} ... sy_{i,d}.
	// it will be a d * merkleTreeHeight array
	MerkleProofY    []frontend.Variable
	MerklePositionY []frontend.Variable
}

func (circuit *BlameCircuit) Define(api frontend.API) error {
	//assert error if privateVec is empty

	// step 1: check the commitment

	hash, _ := mimc.NewMiMC(api)
	for i := 0; i < len(circuit.PrivateX); i++ {
		hash.Write(circuit.PrivateX[i])
	}
	hash.Write(circuit.PrivateMask)
	hash.Write(circuit.PrivateSalt)
	api.AssertIsEqual(circuit.PublicCommitment, hash.Sum())

	// step 2: check the product of the privateY and privateMask
	prod := frontend.Variable(1)
	for i := 0; i < len(circuit.PrivateY); i++ {
		prod = api.Mul(prod, circuit.PrivateY[i])
	}
	api.AssertIsEqual(prod, circuit.PrivateMask)

	// step 3: check the commitment of the serial numbers
	for i := 0; i < len(circuit.PrivateX); i++ {
		hash, _ := mimc.NewMiMC(api)
		hash.Write(circuit.SerialNumX[i])
		hash.Write(circuit.BetaX[i])
		api.AssertIsEqual(circuit.CommSrnX[i], hash.Sum())
	}

	for i := 0; i < len(circuit.PrivateY); i++ {
		hash, _ := mimc.NewMiMC(api)
		hash.Write(circuit.SerialNumY[i])
		hash.Write(circuit.BetaY[i])
		api.AssertIsEqual(circuit.CommSrnY[i], hash.Sum())
	}

	// step 4: check the validity of the merkle proofs for CommSrnX_{i,1} ... CommSrnX_{i,m}
	for i := 0; i < len(circuit.PrivateX); i++ {
		currentHash := circuit.CommSrnX[i]
		for j := 0; j < MerkleTreeHeight; j++ {
			// if the position is 0, then it is the left child
			// otherwise, it is the right child
			hash, _ := mimc.NewMiMC(api)
			pos := circuit.MerklePositionX[i*MerkleTreeHeight+j]
			rightVal := api.Select(pos, currentHash, circuit.MerkleProofX[i*MerkleTreeHeight+j])
			leftVal := api.Sub(api.Add(currentHash, circuit.MerkleProofX[i*MerkleTreeHeight+j]), rightVal) // currentHash + proof - rightVal
			hash.Write(leftVal)
			hash.Write(rightVal)
			currentHash = hash.Sum()
		}
		api.AssertIsEqual(currentHash, circuit.MerkleRootX)
	}

	// step 5: check the validity of the merkle proofs for CommSrnY_{i,1} ... CommSrnY_{i,d}
	for i := 0; i < len(circuit.PrivateY); i++ {
		currentHash := circuit.CommSrnY[i]
		for j := 0; j < MerkleTreeHeight; j++ {
			// if the position is 0, then it is the left child
			// otherwise, it is the right child
			hash, _ := mimc.NewMiMC(api)
			pos := circuit.MerklePositionY[i*MerkleTreeHeight+j]
			rightVal := api.Select(pos, currentHash, circuit.MerkleProofY[i*MerkleTreeHeight+j])
			leftVal := api.Sub(api.Add(currentHash, circuit.MerkleProofY[i*MerkleTreeHeight+j]), rightVal) // currentHash + proof - rightVal
			hash.Write(leftVal)
			hash.Write(rightVal)
			currentHash = hash.Sum()
		}
		api.AssertIsEqual(currentHash, circuit.MerkleRootY)
	}
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
	proof         *groth16.Proof
	SerialNumX    []fr_bn254.Element
	SerialNumY    []fr_bn254.Element
}

type ClientSubmissionToServerPlonk struct {
	publicWitness *witness.Witness
	proof         *plonk.Proof
	SerialNumX    []fr_bn254.Element
	SerialNumY    []fr_bn254.Element
}

type SetAccumulator struct {
	Tree []fr_bn254.Element
	// The tree stores like this
	// 1
	// 2 3
	// 4 5 6 7
	// 8 9 10 11 12 13 14 15
	// there are 2^h real elements in the last level

	ElemToIndex map[fr_bn254.Element]uint64
}

// define a function called "Build" for SetAccumulator
func (acc *SetAccumulator) Build(inputSet []fr_bn254.Element) {
	// first, place the inputSet into the tree
	acc.Tree = make([]fr_bn254.Element, 1<<(MerkleTreeHeight+1))
	for i := 0; i < len(inputSet); i++ {
		acc.Tree[(1<<MerkleTreeHeight)+i] = inputSet[i]
	}
	// place the zeros
	for i := len(inputSet); i < (1 << MerkleTreeHeight); i++ {
		acc.Tree[(1<<MerkleTreeHeight)+i] = fr_bn254.NewElement(uint64(0))
	}

	// now build the tree
	for i := (1 << MerkleTreeHeight) - 1; i > 0; i-- {
		goMimc := hash.MIMC_BN254.New()
		leftVal := acc.Tree[2*i].Bytes()
		rightVal := acc.Tree[2*i+1].Bytes()
		goMimc.Write(leftVal[:])
		goMimc.Write(rightVal[:])
		acc.Tree[i].SetBytes(goMimc.Sum(nil))
	}

	// now build the map
	acc.ElemToIndex = make(map[fr_bn254.Element]uint64)
	for i := 0; i < len(inputSet); i++ {
		//log.Printf("i = %v, inputSet[i] = %v, set index = %v\n", i, inputSet[i], (1 << MerkleTreeHeight) + i)
		acc.ElemToIndex[inputSet[i]] = uint64((1 << MerkleTreeHeight) + i)
	}
}

func (acc *SetAccumulator) GetRoot() fr_bn254.Element {
	return acc.Tree[1]
}

func (acc *SetAccumulator) GetMerkleProof(elem fr_bn254.Element) ([]fr_bn254.Element, []uint64) {
	// first, check if the element is in the set
	//log.Printf("the element is %v\n", elem)
	//log.Printf("size of the acc.map is %v\n", len(acc.ElemToIndex))
	if _, ok := acc.ElemToIndex[elem]; !ok {
		log.Printf("the element is not in the set\n")
		return nil, nil
	}

	posVec := make([]uint64, MerkleTreeHeight)
	proofBranch := make([]fr_bn254.Element, MerkleTreeHeight)

	// now get the merkle proof
	index := acc.ElemToIndex[elem]
	for i := 0; i < MerkleTreeHeight; i++ {
		//log.Printf("i =  %v, index = %v\n", i, index)
		posVec[i] = index % 2
		proofBranch[i] = acc.Tree[index^1]
		index = index >> 1
	}

	return proofBranch, posVec
}

type ClientState struct {
	PrivateX   []fr_bn254.Element
	SerialNumX []fr_bn254.Element
	BetaX      []fr_bn254.Element
	CommSrnX   []fr_bn254.Element

	PrivateY   []fr_bn254.Element
	SerialNumY []fr_bn254.Element
	BetaY      []fr_bn254.Element
	CommSrnY   []fr_bn254.Element

	PublicCom   fr_bn254.Element
	PrivateMask fr_bn254.Element
	PrivateSalt fr_bn254.Element
}

func (c *ClientState) Init(val uint64) {
	c.PrivateX = make([]fr_bn254.Element, PrivateVecLength)
	c.SerialNumX = make([]fr_bn254.Element, PrivateVecLength)
	c.BetaX = make([]fr_bn254.Element, PrivateVecLength)
	c.CommSrnX = make([]fr_bn254.Element, PrivateVecLength)

	c.PrivateY = make([]fr_bn254.Element, DummyVecLength)
	c.SerialNumY = make([]fr_bn254.Element, DummyVecLength)
	c.BetaY = make([]fr_bn254.Element, DummyVecLength)
	c.CommSrnY = make([]fr_bn254.Element, DummyVecLength)

	// first set the privateX. They are random values subject to the constraint that their sum is val
	c.PrivateX[0] = fr_bn254.NewElement(val)
	for i := 1; i < len(c.PrivateX); i++ {
		c.PrivateX[i] = randomFr()
		c.PrivateX[0].Sub(&c.PrivateX[0], &c.PrivateX[i])
	}

	// now set the serial numbers. They are random values
	// the betaX are random values
	// the commitment are the hash of the serial numbers, the betaX and the salt
	for i := 0; i < len(c.SerialNumX); i++ {
		c.SerialNumX[i] = randomFr()
		c.BetaX[i] = randomFr()

		goMimc := hash.MIMC_BN254.New()
		b := c.SerialNumX[i].Bytes()
		goMimc.Write(b[:])
		b = c.BetaX[i].Bytes()
		goMimc.Write(b[:])
		c.CommSrnX[i].SetBytes(goMimc.Sum(nil))
	}

	// now set the privateY. They are random values with no constraint
	for i := 0; i < len(c.PrivateY); i++ {
		c.PrivateY[i] = randomFr()
	}

	// now set the serial numbers. They are random values
	// the betaY are random values
	// the commitment are the hash of the serial numbers, the betaY and the salt
	for i := 0; i < len(c.SerialNumY); i++ {
		c.SerialNumY[i] = randomFr()
		c.BetaY[i] = randomFr()

		goMimc := hash.MIMC_BN254.New()
		b := c.SerialNumY[i].Bytes()
		goMimc.Write(b[:])
		b = c.BetaY[i].Bytes()
		goMimc.Write(b[:])
		c.CommSrnY[i].SetBytes(goMimc.Sum(nil))
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

func (acc *SetAccumulator) VerifyMerkleProof(element fr_bn254.Element, proof []fr_bn254.Element, positions []uint64) bool {
	if len(proof) != MerkleTreeHeight {
		log.Printf("the length of the proof is %v\n", len(proof))
		return false
	}
	//log.Printf("tree = %v", acc.Tree)
	//log.Printf("positions = %v\n", positions)
	//log.Printf("proof = %v\n", proof)
	for i := 0; i < len(proof); i++ {
		if positions[i] == 1 {
			goMimc := hash.MIMC_BN254.New()
			b := proof[i].Bytes()
			goMimc.Write(b[:])
			b = element.Bytes()
			goMimc.Write(b[:])
			element.SetBytes(goMimc.Sum(nil))
		} else {
			goMimc := hash.MIMC_BN254.New()
			b := element.Bytes()
			goMimc.Write(b[:])
			b = proof[i].Bytes()
			goMimc.Write(b[:])
			element.SetBytes(goMimc.Sum(nil))
		}

		//log.Printf("element = %v\n", element)
	}

	root := acc.GetRoot()
	return element.Equal(&root)
}
func (c *ClientState) GenAssignment(setX *SetAccumulator, setY *SetAccumulator) BlameCircuit {
	// build the merkle proofs for the serial numbers
	merkleProofX := make([]fr_bn254.Element, len(c.SerialNumX)*MerkleTreeHeight)
	merklePositionX := make([]uint64, len(c.SerialNumX)*MerkleTreeHeight)
	for i := 0; i < len(c.SerialNumX); i++ {
		proofBranch, posVec := setX.GetMerkleProof(c.CommSrnX[i])
		//log.Printf("the length of the proof branch is %v\n", len(proofBranch))
		//log.Printf("the length of the posVec is %v\n", len(posVec))
		for j := 0; j < len(proofBranch); j++ {
			merkleProofX[i*MerkleTreeHeight+j] = proofBranch[j]
			merklePositionX[i*MerkleTreeHeight+j] = posVec[j]
		}
	}

	if !setX.VerifyMerkleProof(c.CommSrnX[0], merkleProofX[:MerkleTreeHeight], merklePositionX[:MerkleTreeHeight]) {
		log.Printf("the first merkle proof is wrong\n")
	}

	merkleProofY := make([]fr_bn254.Element, len(c.SerialNumY)*MerkleTreeHeight)
	merklePositionY := make([]uint64, len(c.SerialNumY)*MerkleTreeHeight)
	for i := 0; i < len(c.SerialNumY); i++ {
		proofBranch, posVec := setY.GetMerkleProof(c.CommSrnY[i])
		for j := 0; j < len(proofBranch); j++ {
			merkleProofY[i*MerkleTreeHeight+j] = proofBranch[j]
			merklePositionY[i*MerkleTreeHeight+j] = posVec[j]
		}
	}

	// translate PrivateX, SerialNumX, BetaX, CommSrnX, PrivateY, SerialNumY, BetaY, CommSrnY, MerkleProofX, MerklePositionX, MerkleProofY, MerklePositionY into variables
	PrivateXVar := make([]frontend.Variable, len(c.PrivateX))
	SerialNumXVar := make([]frontend.Variable, len(c.SerialNumX))
	BetaXVar := make([]frontend.Variable, len(c.BetaX))
	CommSrnXVar := make([]frontend.Variable, len(c.CommSrnX))
	PrivateYVar := make([]frontend.Variable, len(c.PrivateY))
	SerialNumYVar := make([]frontend.Variable, len(c.SerialNumY))
	BetaYVar := make([]frontend.Variable, len(c.BetaY))
	CommSrnYVar := make([]frontend.Variable, len(c.CommSrnY))
	MerkleProofXVar := make([]frontend.Variable, len(merkleProofX))
	MerklePositionXVar := make([]frontend.Variable, len(merklePositionX))
	MerkleProofYVar := make([]frontend.Variable, len(merkleProofY))
	MerklePositionYVar := make([]frontend.Variable, len(merklePositionY))

	for i := 0; i < len(c.PrivateX); i++ {
		PrivateXVar[i] = frontend.Variable(c.PrivateX[i])
		SerialNumXVar[i] = frontend.Variable(c.SerialNumX[i])
		BetaXVar[i] = frontend.Variable(c.BetaX[i])
		CommSrnXVar[i] = frontend.Variable(c.CommSrnX[i])
	}

	for i := 0; i < len(c.PrivateY); i++ {
		PrivateYVar[i] = frontend.Variable(c.PrivateY[i])
		SerialNumYVar[i] = frontend.Variable(c.SerialNumY[i])
		BetaYVar[i] = frontend.Variable(c.BetaY[i])
		CommSrnYVar[i] = frontend.Variable(c.CommSrnY[i])
	}

	for i := 0; i < len(merkleProofX); i++ {
		MerkleProofXVar[i] = frontend.Variable(merkleProofX[i])
		MerklePositionXVar[i] = frontend.Variable(merklePositionX[i])
	}

	for i := 0; i < len(merkleProofY); i++ {
		MerkleProofYVar[i] = frontend.Variable(merkleProofY[i])
		MerklePositionYVar[i] = frontend.Variable(merklePositionY[i])
	}

	// witness definition
	assignment := BlameCircuit{
		// public
		PublicCommitment: frontend.Variable(c.PublicCom),
		MerkleRootX:      frontend.Variable(setX.GetRoot()),
		MerkleRootY:      frontend.Variable(setY.GetRoot()),
		SerialNumX:       SerialNumXVar[:],
		SerialNumY:       SerialNumYVar[:],

		//private
		PrivateSalt:     frontend.Variable(c.PrivateSalt),
		PrivateMask:     frontend.Variable(c.PrivateMask),
		PrivateX:        PrivateXVar[:],
		CommSrnX:        CommSrnXVar[:],
		BetaX:           BetaXVar[:],
		MerkleProofX:    MerkleProofXVar[:],
		MerklePositionX: MerklePositionXVar[:],
		PrivateY:        PrivateYVar[:],
		CommSrnY:        CommSrnYVar[:],
		BetaY:           BetaYVar[:],
		MerkleProofY:    MerkleProofYVar[:],
		MerklePositionY: MerklePositionYVar[:],
	}

	return assignment
}

func GenProofGroth16(assignment BlameCircuit, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (*groth16.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func GenProofPlonk(assignment BlameCircuit, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey) (*plonk.Proof, *witness.Witness) {
	// witness definition
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// plonk: Prove & Verify
	proof, _ := plonk.Prove(*ccs, *pk, witness)

	return &proof, &publicWitness
}

func BlameGroth16() {
	DummyVecLength = int(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	var circuit = BlameCircuit{
		PublicCommitment: 0,
		MerkleRootX:      0,
		MerkleRootY:      0,
		SerialNumX:       make([]frontend.Variable, PrivateVecLength),
		SerialNumY:       make([]frontend.Variable, DummyVecLength),

		PrivateSalt: 0,
		PrivateMask: 0,

		PrivateX: make([]frontend.Variable, PrivateVecLength),
		BetaX:    make([]frontend.Variable, PrivateVecLength),
		CommSrnX: make([]frontend.Variable, PrivateVecLength),

		MerkleProofX:    make([]frontend.Variable, PrivateVecLength*MerkleTreeHeight),
		MerklePositionX: make([]frontend.Variable, PrivateVecLength*MerkleTreeHeight),

		PrivateY: make([]frontend.Variable, DummyVecLength),
		BetaY:    make([]frontend.Variable, DummyVecLength),
		CommSrnY: make([]frontend.Variable, DummyVecLength),

		MerkleProofY:    make([]frontend.Variable, DummyVecLength*MerkleTreeHeight),
		MerklePositionY: make([]frontend.Variable, DummyVecLength*MerkleTreeHeight),
	}

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)

	// plonk zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)

	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init(uint64(1000 + noise[i]))
	}
	prepTime := time.Since(start)

	// now assume the main stage is done

	// now the server can see the CommSrnXs and CommSrnYs
	// let's build the set accumulators
	start = time.Now()
	setX := SetAccumulator{}
	setY := SetAccumulator{}
	// the server collects all the CommSrnXs and CommSrnYs
	allCommSrnX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)
	allCommSrnY := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].CommSrnX); j++ {
			allCommSrnX[i*PrivateVecLength+j] = clients[i].CommSrnX[j]
		}
		for j := 0; j < len(clients[i].CommSrnY); j++ {
			allCommSrnY[i*DummyVecLength+j] = clients[i].CommSrnY[j]
		}
	}
	setX.Build(allCommSrnX)
	//log.Printf("the root of the setX is %v\n", setX.GetRoot())
	setY.Build(allCommSrnY)
	//log.Printf("the root of the setY is %v\n", setY.GetRoot())
	serverTime := time.Since(start)

	// now assume the client needs to download their own merkle proofs
	// TODO: add the PIR cost
	PIRCommCost, PIRClientTime, PIRServerTime := BatchPIRCost(
		(len(clients))*(PrivateVecLength+DummyVecLength), // Entry Num
		(BN254Size+1)*MerkleTreeHeight,                   // Entry Size. Each entry is a merkle proof + a position vector
		PrivateVecLength+DummyVecLength,                  // Batch Size. The clients downloads the merkle proofs for the serial numbers.
	)

	// now the clients can compute the assignment
	start = time.Now()
	allAssignment := make([]BlameCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(&setX, &setY)
	}
	prepTime += time.Since(start)

	// now the clients can compute the proofs
	// we only generate proofs for the first MaxNumOfCheckProof clients
	start = time.Now()
	allSubmission := make([]ClientSubmissionToServer, ClientNum)
	for i := 0; i < len(clients); i++ {
		if i < MaxNumOfCheckProof {
			allSubmission[i].proof, allSubmission[i].publicWitness = GenProofGroth16(allAssignment[i], &ccs, &pk)
			allSubmission[i].SerialNumX = clients[i].SerialNumX
			allSubmission[i].SerialNumY = clients[i].SerialNumY
		} else {
			allSubmission[i].proof = nil
			allSubmission[i].publicWitness = nil
			allSubmission[i].SerialNumX = clients[i].SerialNumX
			allSubmission[i].SerialNumY = clients[i].SerialNumY
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

	// the server checks for repeated serial numbers

	// first, the server collects all the serial numbers
	allSerialNumX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)
	allSerialNumY := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].SerialNumX); j++ {
			allSerialNumX[i*PrivateVecLength+j] = allSubmission[i].SerialNumX[j]
		}
		for j := 0; j < len(clients[i].SerialNumY); j++ {
			allSerialNumY[i*DummyVecLength+j] = allSubmission[i].SerialNumY[j]
		}
	}

	// now the server can check for repeated serial numbers
	// if there are repeated serial numbers, then the server will output the index of the repeated serial numbers
	// otherwise, the server will output "no repeated serial numbers"
	// build a map from serial numbers to the index
	start = time.Now()

	serialNumToIndexX := make(map[fr_bn254.Element]uint64)
	serialNumToIndexY := make(map[fr_bn254.Element]uint64)

	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].SerialNumX); j++ {
			srn := allSubmission[i].SerialNumX[j]
			// check if the serial number is in the map
			if _, ok := serialNumToIndexX[srn]; ok {
				// if it is in the map, then we find a repeated serial number
				fmt.Printf("repeated serial number %v in client %v and client %v\n", srn, serialNumToIndexX[srn], i)
			} else {
				// if it is not in the map, then we add it to the map
				serialNumToIndexX[srn] = uint64(i)
			}
		}

		for j := 0; j < len(clients[i].SerialNumY); j++ {
			srn := allSubmission[i].SerialNumY[j]
			// check if the serial number is in the map
			if _, ok := serialNumToIndexY[srn]; ok {
				// if it is in the map, then we find a repeated serial number
				fmt.Printf("repeated serial number %v in client %v and client %v\n", srn, serialNumToIndexY[srn], i)
			} else {
				// if it is not in the map, then we add it to the map
				serialNumToIndexY[srn] = uint64(i)
			}
		}
	}
	serverTime += time.Since(start)

	//now we compute the cost
	log.Printf("=========Blame Phase (Groth16)=========")
	nbConstraints := ccs.GetNbConstraints()
	log.Print("Number of Constraints: ", nbConstraints)

	// now we compute the communication
	// the client sends the public witness and the proof to the server
	// and also PrivateVecLength serial numbers and DummyVecLength serial numbers
	// also the PIR cost
	// in addition, the client already sends the commitments of the serial numbers to the server
	proofRelatedCommCost := proofSize // + publicWitnessSize
	commCost := proofSize + publicWitnessSize + PrivateVecLength*BN254Size*2 + DummyVecLength*BN254Size*2 + PIRCommCost
	log.Printf("=====Communication Cost (bytes)=====\n")
	log.Printf("PIR: %v\n", PIRCommCost)
	log.Printf("Proof: %v\n", proofRelatedCommCost)
	log.Printf("Other: %v\n", commCost-PIRCommCost)
	log.Printf("Total: %v\n", commCost)
	log.Printf("============================\n")

	// now we compute the computation cost
	// 3 parts : prep, proof, PIR
	clientTime := prepTime/time.Duration(ClientNum) + proofTime/time.Duration(MaxNumOfCheckProof) + PIRClientTime
	log.Printf("=====Client Computation Cost=====\n")
	log.Printf("PIR: %v\n", PIRClientTime)
	log.Printf("Preparation: %v\n", prepTime/time.Duration(ClientNum))
	log.Printf("Proof: %v\n", proofTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", clientTime)
	log.Printf("============================\n")

	// now we compute the server time amortized per client
	serverTotalTime := serverTime/time.Duration(ClientNum) + verifyTime/time.Duration(MaxNumOfCheckProof) + PIRServerTime
	log.Printf("=====Server Computation Cost=====\n")
	log.Printf("PIR: %v\n", PIRServerTime)
	log.Printf("Other: %v\n", serverTime/time.Duration(ClientNum))
	log.Printf("Verify: %v\n", verifyTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", serverTotalTime)
	log.Printf("============================\n")

	// now we compute the storage cost
	// the proving key size is the storage cost
	log.Printf("=====Storage Cost=====\n")
	log.Printf("Proving Key: %v\n", provingKeySize)
	log.Printf("============================\n")

	s := fmt.Sprintf("Blame Groth16, %v, %v, %v, %v, %v, %v, %v\n",
		nbConstraints,
		ClientNum,
		ClientNum-CorruptedNum,
		clientTime,
		serverTotalTime,
		commCost,
		provingKeySize)
	file.WriteString(s)
}

func BlamePlonk() {
	DummyVecLength = int(ComputeDummyNum(80, ClientNum, CorruptedNum))
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)

	// define a dummy circuit for Blame
	var circuit = BlameCircuit{
		PublicCommitment: 0,
		MerkleRootX:      0,
		MerkleRootY:      0,
		SerialNumX:       make([]frontend.Variable, PrivateVecLength),
		SerialNumY:       make([]frontend.Variable, DummyVecLength),

		PrivateSalt: 0,
		PrivateMask: 0,

		PrivateX: make([]frontend.Variable, PrivateVecLength),
		BetaX:    make([]frontend.Variable, PrivateVecLength),
		CommSrnX: make([]frontend.Variable, PrivateVecLength),

		MerkleProofX:    make([]frontend.Variable, PrivateVecLength*MerkleTreeHeight),
		MerklePositionX: make([]frontend.Variable, PrivateVecLength*MerkleTreeHeight),

		PrivateY: make([]frontend.Variable, DummyVecLength),
		BetaY:    make([]frontend.Variable, DummyVecLength),
		CommSrnY: make([]frontend.Variable, DummyVecLength),

		MerkleProofY:    make([]frontend.Variable, DummyVecLength*MerkleTreeHeight),
		MerklePositionY: make([]frontend.Variable, DummyVecLength*MerkleTreeHeight),
	}

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

	// define n clients
	start := time.Now()
	clients := make([]ClientState, ClientNum)
	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)
	for i := 0; i < len(clients); i++ {
		clients[i].Init(uint64(1000 + noise[i]))
	}
	prepTime := time.Since(start)

	// now assume the main stage is done

	// now the server can see the CommSrnXs and CommSrnYs
	// let's build the set accumulators
	start = time.Now()
	setX := SetAccumulator{}
	setY := SetAccumulator{}
	// the server collects all the CommSrnXs and CommSrnYs
	allCommSrnX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)
	allCommSrnY := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].CommSrnX); j++ {
			allCommSrnX[i*PrivateVecLength+j] = clients[i].CommSrnX[j]
		}
		for j := 0; j < len(clients[i].CommSrnY); j++ {
			allCommSrnY[i*DummyVecLength+j] = clients[i].CommSrnY[j]
		}
	}
	setX.Build(allCommSrnX)
	//log.Printf("the root of the setX is %v\n", setX.GetRoot())
	setY.Build(allCommSrnY)
	//log.Printf("the root of the setY is %v\n", setY.GetRoot())
	serverTime := time.Since(start)

	// now assume the client needs to download their own merkle proofs
	// TODO: add the PIR cost
	PIRCommCost, PIRClientTime, PIRServerTime := BatchPIRCost(
		(len(clients))*(PrivateVecLength+DummyVecLength), // Entry Num
		(BN254Size+1)*MerkleTreeHeight,                   // Entry Size. Each entry is a merkle proof + a position vector
		PrivateVecLength+DummyVecLength,                  // Batch Size. The clients downloads the merkle proofs for the serial numbers.
	)

	// now the clients can compute the assignment
	start = time.Now()
	allAssignment := make([]BlameCircuit, ClientNum)
	for i := 0; i < len(clients); i++ {
		allAssignment[i] = clients[i].GenAssignment(&setX, &setY)
	}
	prepTime += time.Since(start)

	// now the clients can compute the proofs
	// we only generate proofs for the first MaxNumOfCheckProof clients
	start = time.Now()
	allSubmission := make([]ClientSubmissionToServerPlonk, ClientNum)
	for i := 0; i < len(clients); i++ {
		if i < MaxNumOfCheckProof {
			allSubmission[i].proof, allSubmission[i].publicWitness = GenProofPlonk(allAssignment[i], &ccs, &pk)
			allSubmission[i].SerialNumX = clients[i].SerialNumX
			allSubmission[i].SerialNumY = clients[i].SerialNumY
		} else {
			allSubmission[i].proof = nil
			allSubmission[i].publicWitness = nil
			allSubmission[i].SerialNumX = clients[i].SerialNumX
			allSubmission[i].SerialNumY = clients[i].SerialNumY
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

	// the server now checks for repeated serial numbers
	// first, the server collects all the serial numbers
	allSerialNumX := make([]fr_bn254.Element, ClientNum*PrivateVecLength)
	allSerialNumY := make([]fr_bn254.Element, ClientNum*DummyVecLength)
	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].SerialNumX); j++ {
			allSerialNumX[i*PrivateVecLength+j] = allSubmission[i].SerialNumX[j]
		}
		for j := 0; j < len(clients[i].SerialNumY); j++ {
			allSerialNumY[i*DummyVecLength+j] = allSubmission[i].SerialNumY[j]
		}
	}

	// now the server can check for repeated serial numbers
	// if there are repeated serial numbers, then the server will output the index of the repeated serial numbers
	// otherwise, the server will output "no repeated serial numbers"
	// build a map from serial numbers to the index

	start = time.Now()
	serialNumToIndexX := make(map[fr_bn254.Element]uint64)
	serialNumToIndexY := make(map[fr_bn254.Element]uint64)

	for i := 0; i < len(clients); i++ {
		for j := 0; j < len(clients[i].SerialNumX); j++ {
			srn := allSubmission[i].SerialNumX[j]
			// check if the serial number is in the map
			if _, ok := serialNumToIndexX[srn]; ok {
				// if it is in the map, then we find a repeated serial number
				fmt.Printf("repeated serial number %v in client %v and client %v\n", srn, serialNumToIndexX[srn], i)
			} else {
				// if it is not in the map, then we add it to the map
				serialNumToIndexX[srn] = uint64(i)
			}
		}

		for j := 0; j < len(clients[i].SerialNumY); j++ {
			srn := allSubmission[i].SerialNumY[j]
			// check if the serial number is in the map
			if _, ok := serialNumToIndexY[srn]; ok {
				// if it is in the map, then we find a repeated serial number
				fmt.Printf("repeated serial number %v in client %v and client %v\n", srn, serialNumToIndexY[srn], i)
			} else {
				// if it is not in the map, then we add it to the map
				serialNumToIndexY[srn] = uint64(i)
			}
		}
	}
	serverTime += time.Since(start)

	//now we compute the cost

	log.Printf("=========Blame Phase (Plonk)=========")
	nbConstraints := ccs.GetNbConstraints()
	log.Print("Number of Constraints: ", nbConstraints)
	// now we compute the communication
	// the client sends the public witness and the proof to the server
	// and also PrivateVecLength serial numbers and DummyVecLength serial numbers
	// also the PIR cost
	// in addition, the client already sends the commitments of the serial numbers to the server
	commCost := proofSize + publicWitnessSize + PrivateVecLength*BN254Size*2 + DummyVecLength*BN254Size*2 + PIRCommCost
	log.Printf("=====Communication Cost (bytes)=====\n")
	log.Printf("PIR: %v\n", PIRCommCost)
	log.Printf("Other: %v\n", commCost-PIRCommCost)
	log.Printf("Total: %v\n", commCost)
	log.Printf("============================\n")

	// now we compute the computation cost
	// 3 parts : prep, proof, PIR
	clientTime := prepTime/time.Duration(ClientNum) + proofTime/time.Duration(MaxNumOfCheckProof) + PIRClientTime
	log.Printf("=====Client Computation Cost=====\n")
	log.Printf("PIR: %v\n", PIRClientTime)
	log.Printf("Preparation: %v\n", prepTime/time.Duration(ClientNum))
	log.Printf("Proof: %v\n", proofTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", clientTime)
	log.Printf("============================\n")

	// now we compute the server time amortized per client
	serverTotalTime := serverTime/time.Duration(ClientNum) + verifyTime/time.Duration(MaxNumOfCheckProof) + PIRServerTime
	log.Printf("=====Server Computation Cost=====\n")
	log.Printf("PIR: %v\n", PIRServerTime)
	log.Printf("Other: %v\n", serverTime/time.Duration(ClientNum))
	log.Printf("Verify: %v\n", verifyTime/time.Duration(MaxNumOfCheckProof))
	log.Printf("Total: %v\n", serverTotalTime)
	log.Printf("============================\n")

	// now we compute the storage cost
	// the proving key size is the storage cost
	log.Printf("=====Storage Cost=====\n")
	log.Printf("Proving Key: %v\n", provingKeySize)
	log.Printf("============================\n")

	s := fmt.Sprintf("Blame Plonk, %v, %v, %v, %v, %v, %v, %v\n",
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
	pdf := make([]float64, 500)

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
	file, err = os.OpenFile("output-blame.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
	if err != nil {
		panic(err)
	}

	defer file.Close()

	file.WriteString("Name, #Const, #Client, #Honest, Client Time, Server Time, Comm Cost, Proving Key Size\n")

	for t := 0; t < TestRepeat; t++ {
		BlameGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		BlamePlonk()
	}
}
