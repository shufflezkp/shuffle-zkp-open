package main

import (
	"bytes"
	"fmt"
	"log"
	"math"
	"math/rand"
	"time"
	"os"

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
	PublicThreshold = 1500
	ClientNum       = 1000
	CorruptedNum    = 500
	e               = 2.71828182845904523536028747135266249775724709369995
	BN254Size       = 32
	CommitmentSize  = 32
	eps = 1.0
	MaxNumOfCheckProof = 10
	TestRepeat = 5
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

type sumAndCmpCircuit struct {
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

func (circuit *sumAndCmpCircuit) Define(api frontend.API) error {
	//assert error if privateVec is empty

	sum := frontend.Variable(0)

	//sum := circuit.PrivateVec[0]
	//fmt.Printf("circuit.PrivateVec: %v\n", circuit.PrivateVec)
	for i := 0; i < len(circuit.PrivateVec); i++ {
		sum = api.Add(sum, circuit.PrivateVec[i])
		//fmt.Printf("v: %v\n", circuit.PrivateVec[i])
		//fmt.Printf("v: %v\n", sum)
	}
	// compare
	//api.Compiler().ConstantValue()
	//zero := frontend.Variable(fr_bn254.NewElement(uint64(0)))

	zero := frontend.Variable(0)
	//cmpVal := api.Cmp(sum, zero)
	//one := frontend.Variable(1)
	//api.AssertIsEqual(cmpVal, one)

	api.AssertIsLessOrEqual(zero, sum)
	api.AssertIsLessOrEqual(sum, circuit.PublicThreshold)
	//api.AssertIsEqual(zero, sum)
	//api.AssertIsEqual(sum, circuit.PublicThreshold)

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, circuit.PrivateVec, circuit.PublicR)
	privateProd = api.Mul(privateProd, circuit.PrivateMask)
	//privateProd = api.Mul(privateProd, PolyEvalInCircuit(api, circuit.DummyVec, circuit.PublicR))
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	// TODO: check commitment

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

func asb(asdf uint64, asd uint64) (uint64, uint64) {
	return asdf, asd
}

func GenProofGroth16(secretVal []fr_bn254.Element, publicRFr fr_bn254.Element, mask fr_bn254.Element,
	com fr_bn254.Element, salt fr_bn254.Element, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey,
	realProof bool) ClientSubmissionToServer {
	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	//publicR := frontend.Variable(publicRFr)
	secretValVar := make([]frontend.Variable, len(secretVal))
	for i := 0; i < len(secretVal); i++ {
		secretValVar[i] = frontend.Variable(secretVal[i])
	}
	privateProdFr := PolyEval(secretVal[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateProdFr, &mask)

	// witness definition
	assignment := sumAndCmpCircuit{
		PrivateVec:       secretValVar[:],
		PublicThreshold:  frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		PrivateMask:      frontend.Variable(mask),
		PublicR:          frontend.Variable(publicRFr),
		PublicProd:       frontend.Variable(publicProdFr),
		PublicCommitment: frontend.Variable(com),
		PrivateSalt:      frontend.Variable(salt),
	}

	if realProof {
		witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
		//fmt.Println(witness)
		publicWitness, _ := witness.Public()

		// groth16: Prove & Verify
		proof, _ := groth16.Prove(*ccs, *pk, witness)

		return ClientSubmissionToServer{
			publicWitness: &publicWitness,
			publicProd:    publicProdFr,
			proof:         &proof,
		}
	} else  {
		return ClientSubmissionToServer{
			publicWitness: nil,
			publicProd:    publicProdFr,
			proof:         nil,
		}
	}
}

func GenProofPlonk(secretVal []fr_bn254.Element, publicRFr fr_bn254.Element, mask fr_bn254.Element,
	com fr_bn254.Element, salt fr_bn254.Element, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey,
	realProof bool) ClientSubmissionToServerPlonk {
	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	//publicR := frontend.Variable(publicRFr)
	secretValVar := make([]frontend.Variable, len(secretVal))
	for i := 0; i < len(secretVal); i++ {
		secretValVar[i] = frontend.Variable(secretVal[i])
	}
	privateProdFr := PolyEval(secretVal[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateProdFr, &mask)

	// witness definition
	assignment := sumAndCmpCircuit{
		PrivateVec:       secretValVar[:],
		PublicThreshold:  frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		PrivateMask:      frontend.Variable(mask),
		PublicR:          frontend.Variable(publicRFr),
		PublicProd:       frontend.Variable(publicProdFr),
		PublicCommitment: frontend.Variable(com),
		PrivateSalt:      frontend.Variable(salt),
	}
	if realProof {

		witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
		//fmt.Println(witness)
		publicWitness, _ := witness.Public()

		// groth16: Prove & Verify
		proof, _ := plonk.Prove(*ccs, *pk, witness)

		return ClientSubmissionToServerPlonk{
			publicWitness: &publicWitness,
			publicProd:    publicProdFr,
			proof:         &proof,
		}
	} else {
		return ClientSubmissionToServerPlonk{
			publicWitness: nil,
			publicProd:    publicProdFr,
			proof:         nil,
		}
	}
}

/*

func SplitAndShareWithProof(secretVal uint64, publicRFr fr_bn254.Element, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey) (ClientSubmissionToShuffler, ClientSubmissionToServer) {
	// just create a private Vec
	var privateValFr = fr_bn254.NewElement(secretVal)
	var privateVecFr [PrivateVecLength]fr_bn254.Element
	var privateVec [PrivateVecLength]frontend.Variable
	privateVecFr[0] = privateValFr
	for i := 1; i < len(privateVecFr); i++ {
		privateVecFr[i] = randomFr()
		//privateVecFr[i] = fr_bn254.NewElement(uint64(0))
		privateVec[i] = frontend.Variable(privateVecFr[i])
		privateVecFr[0].Sub(&privateVecFr[0], &privateVecFr[i])
	}
	privateVec[0] = frontend.Variable(privateVecFr[0])

	//cnt := privateVecFr[0]
	//for i := 1; i < len(privateVecFr); i++ {
	//	cnt.Add(&cnt, &privateVecFr[i])
	//	}
	//fmt.Printf("cnt: %v\n", cnt.Uint64())
	//assert.Equal()

	var dummyVecFr [DummyVecLength]fr_bn254.Element
	var dummyVec [DummyVecLength]frontend.Variable
	for i := 0; i < len(dummyVecFr); i++ {
		//dummyVecFr[i].SetUint64(uint64(i * 10))
		dummyVecFr[i] = randomFr()
		//dummyVecFr[i] = fr_bn254.NewElement(uint64(i * 10))
		dummyVec[i] = frontend.Variable(dummyVecFr[i])
	}

	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	publicR := frontend.Variable(publicRFr)
	privateProdFr := PolyEval(privateVecFr[:], publicRFr)
	dummyProdFr := PolyEval(dummyVecFr[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateProdFr, &dummyProdFr)
	publicProd := frontend.Variable(publicProdFr)

	//convert dummyVecFr to Variable
	var dummyVecVar [len(dummyVecFr)]frontend.Variable
	for i := 0; i < len(dummyVecFr); i++ {
		dummyVecVar[i] = frontend.Variable(dummyVecFr[i])
	}

	// witness definition
	assignment := sumAndCmpCircuit{
		PrivateVec:      privateVec[:],
		PublicThreshold: frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		DummyVec:        dummyVecVar[:],
		PublicR:         publicR,
		PublicProd:      publicProd,
	}
	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	//fmt.Println(witness)
	publicWitness, _ := witness.Public()

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	submissionToShuffler := ClientSubmissionToShuffler{
		privateVec: privateVecFr,
		dummyVec:   dummyVecFr,
	}

	submissionToServer := ClientSubmissionToServer{
		publicWitness: publicWitness,
		publicProd:    publicProdFr,
		proof:         proof,
	}

	return submissionToShuffler, submissionToServer
}
*/

func ShuffleZKGroth16() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)
	/*
		var a, b fr_bn254.Element
		a.SetInt64(1)
		b.SetInt64(1)
		a.Add(&a, &b)
		fmt.Printf("a: %v\n", a)
		c := a.Uint64()
		fmt.Printf("c: %v\n", c)
		return
	*/

	privateVec := make([]frontend.Variable, PrivateVecLength)
	//var dummyVec [DummyVecLength]frontend.Variable
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	//for i := 0; i < len(dummyVec); i++ {
	//	dummyVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	//	}
	//for i := 0; i < len(array); i++ {
	//	array[i] = frontend.Variable(fr_bn254.NewElement(uint64(i)))
	//	}

	//array := [...]frontend.Variable{1, 2, 3, 4, 5}
	var circuit = sumAndCmpCircuit{
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

	// plonk zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)

	var buf bytes.Buffer
	pk.WriteTo(&buf)
	// check how many bytes are written
	provingKeySize := buf.Len()
	// clean the buffer
	buf.Reset()

	// for clients, each client has a private value
	secretVal := make([]uint64, ClientNum)
	splittedSecretVal := make([][]fr_bn254.Element, ClientNum)
	secretMask := make([]fr_bn254.Element, ClientNum)
	splittedSecretMask := make([][]fr_bn254.Element, ClientNum)
	commitment := make([]fr_bn254.Element, ClientNum)
	secretSalt := make([]fr_bn254.Element, ClientNum)

	//var secretVal [ClientNum]uint64
	//var splittedSecretVal [ClientNum][PrivateVecLength]fr_bn254.Element
	//var secretMask [ClientNum]fr_bn254.Element
	//splittedSecretMask := make([]fr_bn254.Element, ClientNum)
	//var splittedSecretMask [ClientNum][DummyVecLength]fr_bn254.Element
	//var commitment [ClientNum]fr_bn254.Element
	//var secretSalt [ClientNum]fr_bn254.Element

	var allSecretVal []fr_bn254.Element
	var allMask []fr_bn254.Element
	var allProof []ClientSubmissionToServer

	//var clientVal []uint64

	// set up the clients' inputs

	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)

	for i := 0; i < ClientNum; i++ {
		// client i has a private value
		secretVal[i] = uint64(1000 + noise[i])
		if (secretVal[i] > PublicThreshold) {
			log.Printf("out of range: noise = %v\n", noise[i])
		}
	}

	// Step 1:
	// Each client splits its secret vals into mulitple shares.
	// Also, it generates the mulitple masks and compute the product of the masks.
	// It commits to those masks vals and those masks then sends the commitments to the server.

	start := time.Now()

	for i := 0; i < ClientNum; i++ {
		// split the secret value
		splittedSecretVal[i] = make([]fr_bn254.Element, PrivateVecLength)
		splittedSecretVal[i][0] = fr_bn254.NewElement(secretVal[i])
		for j := 1; j < len(splittedSecretVal[i]); j++ {
			splittedSecretVal[i][j] = randomFr()
			splittedSecretVal[i][0].Sub(&splittedSecretVal[i][0], &splittedSecretVal[i][j])
		}

		secretMask[i] = fr_bn254.One()
		splittedSecretMask[i] = make([]fr_bn254.Element, DummyVecLength)
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			splittedSecretMask[i][j] = randomFr()
			secretMask[i].Mul(&secretMask[i], &splittedSecretMask[i][j])
		}

		// compute the commitment
		secretSalt[i] = randomFr()
		goMimc := hash.MIMC_BN254.New()
		for j := 0; j < len(splittedSecretVal[i]); j++ {
			b := splittedSecretVal[i][j].Bytes()
			goMimc.Write(b[:])
		}
		b := secretMask[i].Bytes()
		goMimc.Write(b[:])
		b = secretSalt[i].Bytes()
		goMimc.Write(b[:])
		commitment[i].SetBytes(goMimc.Sum(nil))
		//secretSalt[i] = randomFr()
		//log.Printf("commitment: %v\n", commitment[i])

		// submit the splitted secret val and the splitted secret mask to the shuffler
		allSecretVal = append(allSecretVal, splittedSecretVal[i][:]...)
		allMask = append(allMask, splittedSecretMask[i][:]...)
	}

	prepTime := time.Since(start)

	dummyCostPerClient := DummyVecLength * BN254Size

	//shuffle the allSecretVal and allMask
	rand.Shuffle(len(allSecretVal), func(i, j int) {
		allSecretVal[i], allSecretVal[j] = allSecretVal[j], allSecretVal[i]
	})
	rand.Shuffle(len(allMask), func(i, j int) {
		allMask[i], allMask[j] = allMask[j], allMask[i]
	})

	// now the server can see the shuffled allSecretVal and allMask and also the commitments

	// Step 2:
	// The server generates a public challenge and broadcasts it to all the clients.
	publicRFr := randomFr()

	// Step 3:
	// Each client computes the public witness and the public product and sends them to the server.

	start = time.Now()

	// this counted as proving time
	for i := 0; i < ClientNum; i++ {
		realProof := false
		if i < MaxNumOfCheckProof {
			realProof = true
		}
		//toShuffler, toServer := SplitAndShareWithProof(uint64(secretVal), publicRFr, &ccs, &pk)
		toServer := GenProofGroth16(splittedSecretVal[i][:], publicRFr, secretMask[i], commitment[i], secretSalt[i], &ccs, &pk, realProof)
		//allSecretVal = append(allSecretVal, toShuffler.privateVec[:]...)
		//allDummyVal = append(allDummyVal, toShuffler.dummyVec[:]...)
		allProof = append(allProof, toServer)
	}

	(*(allProof[0].proof)).WriteTo(&buf)
	// check how many bytes are written
	proofSize := buf.Len()
	// clean the buffer
	buf.Reset()

	(*(allProof[0].publicWitness)).WriteTo(&buf)
	// check how many bytes are written
	publicWitnessSize := buf.Len()
	// clean the buffer
	buf.Reset()

	proving_time := time.Since(start)
	start = time.Now()

	// Step 4:
	// The server now sees all the secret values and dummy values.
	// It first verifies all the proof
	// It also computes the product of all the publicProd

	prodFromClients := fr_bn254.NewElement(uint64(1))
	for i := 0; i < ClientNum; i++ {
		if i < MaxNumOfCheckProof {
			verification_err := groth16.Verify(*allProof[i].proof, vk, *allProof[i].publicWitness)
			if verification_err != nil {
				fmt.Printf("verification error in client %v", i)
			}
		}
		prodFromClients.Mul(&prodFromClients, &allProof[i].publicProd)
	}

	verifying_time_only_proof := time.Since(start)
	start = time.Now()

	// It then computes the product from shufflers
	prodFromShuffler := PolyEval(allSecretVal, publicRFr)
	for i := 0; i < len(allMask); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allMask[i])
	}
	//prodFromShuffler.Mul(&prodFromShuffler, &dummyProdFromShuffler)
	if prodFromShuffler.Equal(&prodFromClients) {
		fmt.Printf("server: the set from clients is the same as the set from shuffler\n")
	} else {
		fmt.Printf("server: the set from clients is NOT the same as the set from shuffler\n")
	}

	verifying_time := time.Since(start)

	// the server then computes the sum of all the secret values
	sum := fr_bn254.NewElement(uint64(0))
	for i := 0; i < len(allSecretVal); i++ {
		sum.Add(&sum, &allSecretVal[i])
	}


	fmt.Printf("The computed sum is %v\n", sum.Uint64())

	log.Printf("Task: DP-Shuffle-Sum; Proof System: Groth16\n")
	log.Printf("proving time: %v\n", proving_time)
	log.Printf("Per client proving time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof))
	log.Printf("Per client compute time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum))
	log.Printf("verifying time (only verifying %v proofs): %v\n", MaxNumOfCheckProof, verifying_time)
	log.Printf("Per client verifying time: %v\n", verifying_time_only_proof / time.Duration(MaxNumOfCheckProof) + verifying_time / time.Duration(ClientNum))

	log.Printf("Client Communication Cost (bytes):")
	log.Printf("Proving Key %v\n", provingKeySize)
	log.Printf("To Shuffler %v\n", dummyCostPerClient)
	log.Printf("To Server %v\n", proofSize+publicWitnessSize+CommitmentSize+BN254Size) // a commitment, a public prod, a proof, a public witness
	log.Printf("Proof Size %v\n", proofSize)

	clientTime := proving_time / time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum)
	amtServerTime := verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof)
	commCost := (float64(dummyCostPerClient) + float64(proofSize)+float64(publicWitnessSize)+float64(CommitmentSize)+float64(BN254Size) ) / 1024
	//commCost := dummyCostPerClient + proofSize+publicWitnessSize+CommitmentSize+BN254Size

	file.WriteString(fmt.Sprintf("Shuffle-DP Sum Groth16, %v, %v, %v, %v\n", ClientNum - CorruptedNum, clientTime, amtServerTime, commCost))
}

func ShuffleZKPlonk() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)
	/*
		var a, b fr_bn254.Element
		a.SetInt64(1)
		b.SetInt64(1)
		a.Add(&a, &b)
		fmt.Printf("a: %v\n", a)
		c := a.Uint64()
		fmt.Printf("c: %v\n", c)
		return
	*/

	privateVec := make([]frontend.Variable, PrivateVecLength)
	//var dummyVec [DummyVecLength]frontend.Variable
	for i := 0; i < len(privateVec); i++ {
		privateVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	//for i := 0; i < len(dummyVec); i++ {
	//	dummyVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	//	}
	//for i := 0; i < len(array); i++ {
	//	array[i] = frontend.Variable(fr_bn254.NewElement(uint64(i)))
	//	}

	//array := [...]frontend.Variable{1, 2, 3, 4, 5}
	var circuit = sumAndCmpCircuit{
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

	//publicRFr := fr_bn254.NewElement(uint64(1))

	// for clients, each client has a private value
	secretVal := make([]uint64, ClientNum)
	splittedSecretVal := make([][]fr_bn254.Element, ClientNum)
	secretMask := make([]fr_bn254.Element, ClientNum)
	splittedSecretMask := make([][]fr_bn254.Element, ClientNum)
	commitment := make([]fr_bn254.Element, ClientNum)
	secretSalt := make([]fr_bn254.Element, ClientNum)

	//var secretVal [ClientNum]uint64
	//var splittedSecretVal [ClientNum][PrivateVecLength]fr_bn254.Element
	//var secretMask [ClientNum]fr_bn254.Element
	//splittedSecretMask := make([]fr_bn254.Element, ClientNum)
	//var splittedSecretMask [ClientNum][DummyVecLength]fr_bn254.Element
	//var commitment [ClientNum]fr_bn254.Element
	//var secretSalt [ClientNum]fr_bn254.Element

	var allSecretVal []fr_bn254.Element
	var allMask []fr_bn254.Element
	var allProof []ClientSubmissionToServerPlonk

	//var clientVal []uint64

	// set up the clients' inputs

	//noise := GenDistributedDPNoise()

	noise := GenDistributedDPNoise(eps, 1000.0, ClientNum)
	for i := 0; i < ClientNum; i++ {
		// client i has a private value
		secretVal[i] = uint64(1000 + noise[i])
		if (secretVal[i] > PublicThreshold) {
			log.Printf("out of range: noise = %v\n", noise[i])
		}
	}

	// Step 1:
	// Each client splits its secret vals into mulitple shares.
	// Also, it generates the mulitple masks and compute the product of the masks.
	// It commits to those masks vals and those masks then sends the commitments to the server.

	start := time.Now()

	for i := 0; i < ClientNum; i++ {
		// split the secret value
		splittedSecretVal[i] = make([]fr_bn254.Element, PrivateVecLength)
		splittedSecretVal[i][0] = fr_bn254.NewElement(secretVal[i])
		for j := 1; j < len(splittedSecretVal[i]); j++ {
			splittedSecretVal[i][j] = randomFr()
			splittedSecretVal[i][0].Sub(&splittedSecretVal[i][0], &splittedSecretVal[i][j])
		}

		secretMask[i] = fr_bn254.One()
		splittedSecretMask[i] = make([]fr_bn254.Element, DummyVecLength)
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			splittedSecretMask[i][j] = randomFr()
			secretMask[i].Mul(&secretMask[i], &splittedSecretMask[i][j])
		}

		// compute the commitment
		secretSalt[i] = randomFr()
		goMimc := hash.MIMC_BN254.New()
		for j := 0; j < len(splittedSecretVal[i]); j++ {
			b := splittedSecretVal[i][j].Bytes()
			goMimc.Write(b[:])
		}
		b := secretMask[i].Bytes()
		goMimc.Write(b[:])
		b = secretSalt[i].Bytes()
		goMimc.Write(b[:])
		commitment[i].SetBytes(goMimc.Sum(nil))
		//secretSalt[i] = randomFr()
		//log.Printf("commitment: %v\n", commitment[i])

		// submit the splitted secret val and the splitted secret mask to the shuffler
		allSecretVal = append(allSecretVal, splittedSecretVal[i][:]...)
		allMask = append(allMask, splittedSecretMask[i][:]...)
	}


	prepTime := time.Since(start)

	dummyCostPerClient := DummyVecLength * BN254Size

	//shuffle the allSecretVal and allMask
	rand.Shuffle(len(allSecretVal), func(i, j int) {
		allSecretVal[i], allSecretVal[j] = allSecretVal[j], allSecretVal[i]
	})
	rand.Shuffle(len(allMask), func(i, j int) {
		allMask[i], allMask[j] = allMask[j], allMask[i]
	})

	// now the server can see the shuffled allSecretVal and allMask and also the commitments

	// Step 2:
	// The server generates a public challenge and broadcasts it to all the clients.
	publicRFr := randomFr()

	// Step 3:
	// Each client computes the public witness and the public product and sends them to the server.

	start = time.Now()

	// this counted as proving time
	for i := 0; i < ClientNum; i++ {
		realProof := false
		if i < MaxNumOfCheckProof {
			realProof = true
		}
		//toShuffler, toServer := SplitAndShareWithProof(uint64(secretVal), publicRFr, &ccs, &pk)
		toServer := GenProofPlonk(splittedSecretVal[i][:], publicRFr, secretMask[i], commitment[i], secretSalt[i], &ccs, &pk, realProof)
		//allSecretVal = append(allSecretVal, toShuffler.privateVec[:]...)
		//allDummyVal = append(allDummyVal, toShuffler.dummyVec[:]...)
		allProof = append(allProof, toServer)
	}

	(*(allProof[0].proof)).WriteTo(&buf)
	// check how many bytes are written
	proofSize := buf.Len()
	// clean the buffer
	buf.Reset()

	(*(allProof[0].publicWitness)).WriteTo(&buf)
	// check how many bytes are written
	publicWitnessSize := buf.Len()
	// clean the buffer
	buf.Reset()

	proving_time := time.Since(start)
	start = time.Now()

	// Step 4:
	// The server now sees all the secret values and dummy values.
	// It first verifies all the proof
	// It also computes the product of all the publicProd

	prodFromClients := fr_bn254.NewElement(uint64(1))
	for i := 0; i < ClientNum; i++ {
		//verify proof
		//fmt.Printf("proof: %v
		if i < MaxNumOfCheckProof {
			verification_err := plonk.Verify(*allProof[i].proof, vk, *allProof[i].publicWitness)
			if verification_err != nil {
				fmt.Printf("verification error in client %v", i)
			}
		}
		prodFromClients.Mul(&prodFromClients, &allProof[i].publicProd)
	}

	verifying_time_only_proof := time.Since(start)
	start = time.Now()

	// It then computes the product from shufflers
	prodFromShuffler := PolyEval(allSecretVal, publicRFr)
	for i := 0; i < len(allMask); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &allMask[i])
	}
	//prodFromShuffler.Mul(&prodFromShuffler, &dummyProdFromShuffler)
	if prodFromShuffler.Equal(&prodFromClients) {
		fmt.Printf("server: the set from clients is the same as the set from shuffler\n")
	} else {
		fmt.Printf("server: the set from clients is NOT the same as the set from shuffler\n")
	}

	verifying_time := time.Since(start)

	// the server then computes the sum of all the secret values
	sum := fr_bn254.NewElement(uint64(0))
	for i := 0; i < len(allSecretVal); i++ {
		sum.Add(&sum, &allSecretVal[i])
	}

	fmt.Printf("The computed sum is %v\n", sum.Uint64())

	log.Printf("Task: DP-Shuffle-Sum; Proof System: Plonk")

	log.Printf("proving time: %v\n", proving_time)
	log.Printf("Per client proving time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof))
	log.Printf("verifying time (only verifying %v proofs): %v\n", MaxNumOfCheckProof, verifying_time)
	log.Printf("Per client verifying time: %v\n", verifying_time_only_proof / time.Duration(MaxNumOfCheckProof) + verifying_time / time.Duration(ClientNum))

	log.Printf("Client Communication Cost (bytes):")
	log.Printf("Proving Key %v\n", provingKeySize)
	log.Printf("To Shuffler %v\n", dummyCostPerClient)
	log.Printf("To Server %v\n", proofSize+publicWitnessSize+CommitmentSize+BN254Size) // a commitment, a public prod, a proof, a public witness
	log.Printf("Proof Size %v\n", proofSize)

	clientTime := proving_time / time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum)
	amtServerTime := verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof)
	commCost := (float64(dummyCostPerClient) + float64(proofSize)+float64(publicWitnessSize)+float64(CommitmentSize)+float64(BN254Size) ) / 1024
	//commCost := dummyCostPerClient + proofSize+publicWitnessSize+CommitmentSize+BN254Size

	file.WriteString(fmt.Sprintf("Shuffle-DP Sum Plonk, %v, %v, %v, %v\n", ClientNum - CorruptedNum, clientTime, amtServerTime, commCost))

	/*
		// just create a private Vec

		var privateValFr = fr_bn254.NewElement(uint64(14))
		var privateVecFr [5]fr_bn254.Element
		var privateVec [5]frontend.Variable
		privateVecFr[0] = privateValFr
		for i := 1; i < len(privateVecFr); i++ {
			privateVecFr[i] = randomFr()
			privateVec[i] = frontend.Variable(privateVecFr[i])
			privateVecFr[0].Sub(&privateVecFr[0], &privateVecFr[i])
		}
		privateVec[0] = frontend.Variable(privateVecFr[0])

		cnt := privateVecFr[0]
		for i := 1; i < len(privateVecFr); i++ {
			cnt.Add(&cnt, &privateVecFr[i])
		}
		fmt.Printf("cnt: %v\n", cnt.Uint64())

		var dummyVecFr [2]fr_bn254.Element
		var dummyVec [2]frontend.Variable
		for i := 0; i < len(dummyVecFr); i++ {
			dummyVecFr[i].SetUint64(uint64(i * 10))
			dummyVec[i] = frontend.Variable(dummyVecFr[i])
		}

		//publicRFr := fr_bn254.NewElement(uint64(1))
		publicRFr := randomFr()
		publicR := frontend.Variable(publicRFr)
		privateProdFr := PolyEval(privateVecFr[:], publicRFr)
		dummyProdFr := PolyEval(dummyVecFr[:], publicRFr)
		var publicProdFr fr_bn254.Element
		publicProdFr.Mul(&privateProdFr, &dummyProdFr)
		publicProd := frontend.Variable(publicProdFr)

		//convert dummyVecFr to Variable
		var dummyVecVar [len(dummyVecFr)]frontend.Variable
		for i := 0; i < len(dummyVecFr); i++ {
			dummyVecVar[i] = frontend.Variable(dummyVecFr[i])
		}

		//convert privateVecFr to Variable
		var privateVecVar [5]frontend.Variable
		for i := 0; i < len(privateVecFr); i++ {
			privateVecVar[i] = frontend.Variable(privateVecFr[i])
		}

		//TODO: add a random sample in Fr
		//TODO: convert to Variable

		// witness definition
		assignment := sumAndCmpCircuit{
			PrivateVec:      privateVecVar[:],
			PublicThreshold: frontend.Variable(fr_bn254.NewElement(uint64(15))),
			DummyVec:        dummyVecVar[:],
			PublicR:         publicR,
			PublicProd:      publicProd,
		}
		witness, _ := frontend.NewWitness(&assignment, ecc.BN254)
		fmt.Println(witness)
		publicWitness, _ := witness.Public()

		// groth16: Prove & Verify
		proof, proof_err := groth16.Prove(ccs, pk, witness)
		fmt.Printf("proof error: %v\n", proof_err)

		verification_err := groth16.Verify(proof, vk, publicWitness)

		fmt.Printf("verification error: %v\n", verification_err)
	*/
}



func GenPolyaPDF(r float64, p float64) []float64 {
	// Generate the PDF for distribution Polya(r, p) for k= 0...99
	fmt.Printf("%v %v\n", r, p)
	ptor := math.Pow(p, r)
	t := 1.0
	accu := math.Gamma(r) // accu_k = gamma(k + r) / k!
	prob := 1.0 // the remaining probability
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
	pdf[len(pdf) - 1] += prob // truncate it at 99, move the remaining prob to 0

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
	pdf := GenPolyaPDF(1.0 / float64(n), 1 - math.Exp(-eps / sensitivity))
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

	file.WriteString("Name, Honest Client Num, Client Time, Server Time, Communication Cost\n")


	for t := 0; t < TestRepeat; t++ {
		ShuffleZKGroth16()
	}

	for t := 0; t < TestRepeat; t++ {
		ShuffleZKPlonk()
	}
}
