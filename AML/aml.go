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
)

const (
	// 5 private inputs
	PrivateTxNum    = 200
	PublicThreshold = 10000
	ClientNum       = 1000
	CorruptedNum    = 500
	e               = 2.71828182845904523536028747135266249775724709369995
	BN254Size       = 32
	CommitmentSize  = 32
	TestRepeat      = 5
	MaxNumOfCheckProof = 10
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

type PerAddressCheckCircuit struct {
	PrivateTxs  []PrivateTxVar
	PrivateHash []frontend.Variable
	/*
		PrivateSender []frontend.Variable
		PrivateRecv   []frontend.Variable
		PrivateAmt    []frontend.Variable
		PrivateTxSalt []frontend.Variable
		PrivateHash   []frontend.Variable
	*/

	PublicThreshold frontend.Variable `gnark:",public"`

	// The following are for the polynomial evaluation
	PrivateMask frontend.Variable
	PublicR     frontend.Variable `gnark:",public"`
	PublicProd  frontend.Variable `gnark:",public"`

	// The following are for the commitment
	PublicCommitment frontend.Variable `gnark:",public"`
	PrivateSalt      frontend.Variable
}

func (circuit *PerAddressCheckCircuit) Define(api frontend.API) error {
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

func GenProofGroth16(privateTxs []PrivateTx, privateHash []fr_bn254.Element,
	publicRFr fr_bn254.Element, mask fr_bn254.Element,
	com fr_bn254.Element, salt fr_bn254.Element, ccs *constraint.ConstraintSystem, pk *groth16.ProvingKey,
	realProof bool) ClientSubmissionToServer {
	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	//publicR := frontend.Variable(publicRFr)
	privateTxsVar := make([]PrivateTxVar, len(privateTxs))
	privateHashVar := make([]frontend.Variable, len(privateHash))
	for i := 0; i < len(privateTxs); i++ {
		privateTxsVar[i].Send = frontend.Variable(privateTxs[i].Send)
		privateTxsVar[i].Recv = frontend.Variable(privateTxs[i].Recv)
		privateTxsVar[i].Amt = frontend.Variable(privateTxs[i].Amt)
		privateTxsVar[i].Tx_salt = frontend.Variable(privateTxs[i].Tx_salt)
		privateHashVar[i] = frontend.Variable(privateHash[i])
	}

	privateProdFr := PolyEval(privateHash[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateProdFr, &mask)

	// witness definition
	assignment := PerAddressCheckCircuit{
		PrivateTxs:       privateTxsVar[:],
		PrivateHash:      privateHashVar[:],
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
	} else {
		return ClientSubmissionToServer{
			publicWitness: nil,
			publicProd:    publicProdFr,
			proof:         nil,
		}
	}
}

func GenProofPlonk(privateTxs []PrivateTx, privateHash []fr_bn254.Element,
	publicRFr fr_bn254.Element, mask fr_bn254.Element,
	com fr_bn254.Element, salt fr_bn254.Element, ccs *constraint.ConstraintSystem, pk *plonk.ProvingKey,
	realProof bool) ClientSubmissionToServerPlonk {
	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	//publicR := frontend.Variable(publicRFr)
	privateTxsVar := make([]PrivateTxVar, len(privateTxs))
	privateHashVar := make([]frontend.Variable, len(privateHash))
	for i := 0; i < len(privateTxs); i++ {
		privateTxsVar[i].Send = frontend.Variable(privateTxs[i].Send)
		privateTxsVar[i].Recv = frontend.Variable(privateTxs[i].Recv)
		privateTxsVar[i].Amt = frontend.Variable(privateTxs[i].Amt)
		privateTxsVar[i].Tx_salt = frontend.Variable(privateTxs[i].Tx_salt)
		privateHashVar[i] = frontend.Variable(privateHash[i])
	}

	privateProdFr := PolyEval(privateHash[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateProdFr, &mask)

	// witness definition
	assignment := PerAddressCheckCircuit{
		PrivateTxs:       privateTxsVar[:],
		PrivateHash:      privateHashVar[:],
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
	dummyCostPerClient := DummyVecLength * BN254Size

	//initialize a dummy circuit

	dummyPrivateTxsVar := make([]PrivateTxVar, PrivateTxNum)
	dummyPrivateHashVar := make([]frontend.Variable, PrivateTxNum)

	for i := 0; i < PrivateTxNum; i++ {
		dummyPrivateTxsVar[i] = PrivateTxVar{
			Send:    frontend.Variable(0),
			Recv:    frontend.Variable(0),
			Amt:     frontend.Variable(0),
			Tx_salt: frontend.Variable(0),
		}
		dummyPrivateHashVar[i] = frontend.Variable(0)
	}

	var circuit = PerAddressCheckCircuit{
		PrivateTxs:       dummyPrivateTxsVar[:],
		PrivateHash:      dummyPrivateHashVar[:],
		PublicThreshold:  0,
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

	//publicRFr := fr_bn254.NewElement(uint64(1))

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)

	allPrivateTxs := make([][]PrivateTx, ClientNum)
	allPrivateHash := make([][]fr_bn254.Element, ClientNum)
	privateMask := make([]fr_bn254.Element, ClientNum)
	splittedSecretMask := make([][]fr_bn254.Element, ClientNum)
	privateSalt := make([]fr_bn254.Element, ClientNum)
	commitment := make([]fr_bn254.Element, ClientNum)

	shuffledHash := make([]fr_bn254.Element, ClientNum*PrivateTxNum)
	shuffledMask := make([]fr_bn254.Element, ClientNum*DummyVecLength)

	start := time.Now()

	for i := 0; i < ClientNum; i++ {
		allPrivateTxs[i] = make([]PrivateTx, PrivateTxNum)
		allPrivateHash[i] = make([]fr_bn254.Element, PrivateTxNum)
		for j := 0; j < PrivateTxNum; j++ {
			send := i
			recv := rng.Intn(ClientNum)
			amt := rng.Intn(100)

			allPrivateTxs[i][j].Send = fr_bn254.NewElement(uint64(send))
			allPrivateTxs[i][j].Recv = fr_bn254.NewElement(uint64(recv))
			allPrivateTxs[i][j].Amt = fr_bn254.NewElement(uint64(amt))
			allPrivateTxs[i][j].Tx_salt = randomFr()
			// mimc hash and store the hash
			goMimc := hash.MIMC_BN254.New()
			tmpBytes := allPrivateTxs[i][j].Send.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Recv.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Amt.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Tx_salt.Bytes()
			goMimc.Write(tmpBytes[:])
			allPrivateHash[i][j].SetBytes(goMimc.Sum(nil))
		}

		privateMask[i] = fr_bn254.One()
		splittedSecretMask[i] = make([]fr_bn254.Element, DummyVecLength)
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			splittedSecretMask[i][j] = randomFr()
			privateMask[i].Mul(&privateMask[i], &splittedSecretMask[i][j])
		}

		// compute the commitment
		privateSalt[i] = randomFr()
		goMimc := hash.MIMC_BN254.New()
		for j := 0; j < len(allPrivateHash[i]); j++ {
			b := allPrivateHash[i][j].Bytes()
			goMimc.Write(b[:])
		}
		b := privateMask[i].Bytes()
		goMimc.Write(b[:])
		b = privateSalt[i].Bytes()
		goMimc.Write(b[:])
		commitment[i].SetBytes(goMimc.Sum(nil))

		// append the private hash and the private mask to the shuffled hash and shuffled mask
		for j := 0; j < len(allPrivateHash[i]); j++ {
			shuffledHash[i*PrivateTxNum+j] = allPrivateHash[i][j]
		}
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			shuffledMask[i*int(DummyVecLength)+j] = splittedSecretMask[i][j]
		}
	}

	prepTime := time.Since(start)

	//shuffle the shuffledHash and shuffledMask
	rand.Shuffle(len(shuffledHash), func(i, j int) {
		shuffledHash[i], shuffledHash[j] = shuffledHash[j], shuffledHash[i]
	})
	rand.Shuffle(len(shuffledMask), func(i, j int) {
		shuffledMask[i], shuffledMask[j] = shuffledMask[j], shuffledMask[i]
	})

	// now the server can see the shuffled hash and shuffled mask

	// Step 2:
	// The server generates a public challenge and broadcasts it to all the clients.
	publicRFr := randomFr()

	// Step 3:
	// Each client computes the public witness and the public product and sends them to the server.

	start = time.Now()

	allProof := make([]ClientSubmissionToServer, ClientNum)

	// this counted as proving time
	for i := 0; i < ClientNum; i++ {
		realProof := false
		if i < MaxNumOfCheckProof {
			realProof = true
		}
		//toShuffler, toServer := SplitAndShareWithProof(uint64(secretVal), publicRFr, &ccs, &pk)
		toServer := GenProofGroth16(allPrivateTxs[i], allPrivateHash[i], publicRFr, privateMask[i], commitment[i], privateSalt[i], &ccs, &pk, realProof)
		//allSecretVal = append(allSecretVal, toShuffler.privateVec[:]...)
		//allDummyVal = append(allDummyVal, toShuffler.dummyVec[:]...)
		allProof[i] = toServer
	}
	proving_time := time.Since(start)


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
	prodFromShuffler := PolyEval(shuffledHash, publicRFr)
	for i := 0; i < len(shuffledMask); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &shuffledMask[i])
	}
	//prodFromShuffler.Mul(&prodFromShuffler, &dummyProdFromShuffler)
	if prodFromShuffler.Equal(&prodFromClients) {
		fmt.Printf("server: the set from clients is the same as the set from shuffler\n")
	} else {
		fmt.Printf("server: the set from clients is NOT the same as the set from shuffler\n")
	}

	verifying_time := time.Since(start)

	log.Printf("Task: AML; Proof System: Groth16")
	log.Printf("proving time: %v\n", proving_time)
	log.Printf("Per client proving time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof))
	log.Printf("Per client compute time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum))
	log.Printf("total verifying time (only verifying %v proofs): %v\n", MaxNumOfCheckProof, verifying_time_only_proof + verifying_time)
	log.Printf("Per client verifying time: %v\n", verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof))

	log.Printf("Client Storage/Communication Cost (bytes):")
	log.Printf("Proving Key %v\n", provingKeySize)
	log.Printf("To Shuffler %v\n", dummyCostPerClient)
	log.Printf("To Server %v\n", proofSize+publicWitnessSize+CommitmentSize+BN254Size) // a commitment, a public prod, a proof, a public witness

	clientTime := proving_time / time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum)
	amtServerTime := verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof)
	commCost := (float64(dummyCostPerClient) + float64(proofSize)+float64(publicWitnessSize)+float64(CommitmentSize)+float64(BN254Size) ) / 1024

	file.WriteString(fmt.Sprintf("AML Groth16, %v, %v, %v, %v\n", ClientNum - CorruptedNum, clientTime, amtServerTime, commCost))
}

func ShuffleZKPlonk() {
	DummyVecLength = ComputeDummyNum(80, ClientNum, CorruptedNum)
	log.Printf("lambda %v, n %v, t %v, Dummy Num: %v\n", 80, ClientNum, CorruptedNum, DummyVecLength)
	dummyCostPerClient := DummyVecLength * BN254Size

	//initialize a dummy circuit

	dummyPrivateTxsVar := make([]PrivateTxVar, PrivateTxNum)
	dummyPrivateHashVar := make([]frontend.Variable, PrivateTxNum)

	for i := 0; i < PrivateTxNum; i++ {
		dummyPrivateTxsVar[i] = PrivateTxVar{
			Send:    frontend.Variable(0),
			Recv:    frontend.Variable(0),
			Amt:     frontend.Variable(0),
			Tx_salt: frontend.Variable(0),
		}
		dummyPrivateHashVar[i] = frontend.Variable(0)
	}

	var circuit = PerAddressCheckCircuit{
		PrivateTxs:       dummyPrivateTxsVar[:],
		PrivateHash:      dummyPrivateHashVar[:],
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
	//ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)

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

	source := rand.NewSource(time.Now().UnixNano())
	rng := rand.New(source)

	allPrivateTxs := make([][]PrivateTx, ClientNum)
	allPrivateHash := make([][]fr_bn254.Element, ClientNum)
	privateMask := make([]fr_bn254.Element, ClientNum)
	splittedSecretMask := make([][]fr_bn254.Element, ClientNum)
	privateSalt := make([]fr_bn254.Element, ClientNum)
	commitment := make([]fr_bn254.Element, ClientNum)

	shuffledHash := make([]fr_bn254.Element, ClientNum*PrivateTxNum)
	shuffledMask := make([]fr_bn254.Element, ClientNum*DummyVecLength)

	start := time.Now()

	for i := 0; i < ClientNum; i++ {
		allPrivateTxs[i] = make([]PrivateTx, PrivateTxNum)
		allPrivateHash[i] = make([]fr_bn254.Element, PrivateTxNum)
		for j := 0; j < PrivateTxNum; j++ {
			send := i
			recv := rng.Intn(ClientNum)
			amt := rng.Intn(100)

			allPrivateTxs[i][j].Send = fr_bn254.NewElement(uint64(send))
			allPrivateTxs[i][j].Recv = fr_bn254.NewElement(uint64(recv))
			allPrivateTxs[i][j].Amt = fr_bn254.NewElement(uint64(amt))
			allPrivateTxs[i][j].Tx_salt = randomFr()
			// mimc hash and store the hash
			goMimc := hash.MIMC_BN254.New()
			tmpBytes := allPrivateTxs[i][j].Send.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Recv.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Amt.Bytes()
			goMimc.Write(tmpBytes[:])
			tmpBytes = allPrivateTxs[i][j].Tx_salt.Bytes()
			goMimc.Write(tmpBytes[:])
			allPrivateHash[i][j].SetBytes(goMimc.Sum(nil))
		}

		privateMask[i] = fr_bn254.One()
		splittedSecretMask[i] = make([]fr_bn254.Element, DummyVecLength)
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			splittedSecretMask[i][j] = randomFr()
			privateMask[i].Mul(&privateMask[i], &splittedSecretMask[i][j])
		}

		// compute the commitment
		privateSalt[i] = randomFr()
		goMimc := hash.MIMC_BN254.New()
		for j := 0; j < len(allPrivateHash[i]); j++ {
			b := allPrivateHash[i][j].Bytes()
			goMimc.Write(b[:])
		}
		b := privateMask[i].Bytes()
		goMimc.Write(b[:])
		b = privateSalt[i].Bytes()
		goMimc.Write(b[:])
		commitment[i].SetBytes(goMimc.Sum(nil))

		// append the private hash and the private mask to the shuffled hash and shuffled mask
		for j := 0; j < len(allPrivateHash[i]); j++ {
			shuffledHash[i*PrivateTxNum+j] = allPrivateHash[i][j]
		}
		for j := 0; j < len(splittedSecretMask[i]); j++ {
			shuffledMask[i*int(DummyVecLength)+j] = splittedSecretMask[i][j]
		}
	}

	prepTime := time.Since(start)

	//shuffle the shuffledHash and shuffledMask
	rand.Shuffle(len(shuffledHash), func(i, j int) {
		shuffledHash[i], shuffledHash[j] = shuffledHash[j], shuffledHash[i]
	})
	rand.Shuffle(len(shuffledMask), func(i, j int) {
		shuffledMask[i], shuffledMask[j] = shuffledMask[j], shuffledMask[i]
	})

	// now the server can see the shuffled hash and shuffled mask

	// Step 2:
	// The server generates a public challenge and broadcasts it to all the clients.
	publicRFr := randomFr()

	// Step 3:
	// Each client computes the public witness and the public product and sends them to the server.

	start = time.Now()

	allProof := make([]ClientSubmissionToServerPlonk, ClientNum)

	// this counted as proving time
	for i := 0; i < ClientNum; i++ {
		realProof := false
		if i < MaxNumOfCheckProof {
			realProof = true
		}
		//toShuffler, toServer := SplitAndShareWithProof(uint64(secretVal), publicRFr, &ccs, &pk)
		toServer := GenProofPlonk(allPrivateTxs[i], allPrivateHash[i], publicRFr, privateMask[i], commitment[i], privateSalt[i], &ccs, &pk, realProof)
		//allSecretVal = append(allSecretVal, toShuffler.privateVec[:]...)
		//allDummyVal = append(allDummyVal, toShuffler.dummyVec[:]...)
		allProof[i] = toServer
	}
	proving_time := time.Since(start)


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
	prodFromShuffler := PolyEval(shuffledHash, publicRFr)
	for i := 0; i < len(shuffledMask); i++ {
		prodFromShuffler.Mul(&prodFromShuffler, &shuffledMask[i])
	}
	//prodFromShuffler.Mul(&prodFromShuffler, &dummyProdFromShuffler)
	if prodFromShuffler.Equal(&prodFromClients) {
		fmt.Printf("server: the set from clients is the same as the set from shuffler\n")
	} else {
		fmt.Printf("server: the set from clients is NOT the same as the set from shuffler\n")
	}

	verifying_time := time.Since(start)

	log.Printf("Task: AML; Proof System: Plonk")
	log.Printf("proving time: %v\n", proving_time)
	log.Printf("Per client proving time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof))
	log.Printf("Per client compute time: %v\n", proving_time/time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum))
	log.Printf("total verifying time (only verifying %v proofs): %v\n", MaxNumOfCheckProof, verifying_time_only_proof + verifying_time)
	log.Printf("Per client verifying time: %v\n", verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof))

	log.Printf("Client Storage/Communication Cost (bytes):")
	log.Printf("Proving Key %v\n", provingKeySize)
	log.Printf("To Shuffler %v\n", dummyCostPerClient)
	log.Printf("To Server %v\n", proofSize+publicWitnessSize+CommitmentSize+BN254Size) // a commitment, a public prod, a proof, a public witness

	
	clientTime := proving_time / time.Duration(MaxNumOfCheckProof) + prepTime/time.Duration(ClientNum)
	amtServerTime := verifying_time/time.Duration(ClientNum) + verifying_time_only_proof/time.Duration(MaxNumOfCheckProof)
	commCost := (float64(dummyCostPerClient) + float64(proofSize)+float64(publicWitnessSize)+float64(CommitmentSize)+float64(BN254Size) ) / 1024
	//commCost := dummyCostPerClient + proofSize+publicWitnessSize+CommitmentSize+BN254Size

	file.WriteString(fmt.Sprintf("AML Plonk, %v, %v, %v, %v\n", ClientNum - CorruptedNum, clientTime, amtServerTime, commCost))
}

func main() {
	var err error
	file, err = os.OpenFile("output-aml.csv", os.O_APPEND|os.O_WRONLY|os.O_CREATE, 0600)
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
	//ShuffleZKPlonk()
}
