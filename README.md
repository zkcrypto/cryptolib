# cryptolib

Formal proof of correctness and game-based proof of semantic security for the ElGamal public key encryption protocol using the Lean theorem prover. Our implementation draws from Adam Petcher's Foundational Cryptographic Framework (FCF) Coq library at https://github.com/adampetcher/fcf. My master's dissertation which describes this project in more depth can be found [here](https://1drv.ms/b/s!AkAJTM1hbeSD4wcF1T4NYiRG5b_D?e=0Yp8Hx).

## Install cryptolib

```console
$ git clone https://github.com/JoeyLupo/cryptolib
$ cd cryptolib
$ leanproject build
```

## Files in cryptolib

- `ddh.lean` - provides a formal specification of the decisional Diffie-Hellman assumption on a finite cyclic group
	
- [elgamal.lean](src/elgamal.lean) - contains the formal specification of the ElGamal public key encryption protocol, and the formal proofs of correctness 
    
- `negligible.lean` - defines negligible functions and provides several useful lemmas regarding negligible functions

- [pke.lean](src/pke.lean) - provides formal definitions for correctness and semantic security of a public key encryption scheme

- [tactics.lean](src/tactics.lean) - provides the `bindskip` and `bindconst` tactics to help prove equivalences between pmfs

- [to_mathlib.lean](src/to_mathlib.lean) - includes general lemmas for inclusion into mathlib

- [uniform.lean](src/uniform.lean) - defines the uniform distribution over a finite group as a pmf, including the special case of Z_q, the integers modulo q, and provides two useful lemmas regarding uniform probabilities 

- [rsa.lean](src/rsa.lean) - contains proof of correctness of the RSA public key encryption protocol

- [substitution.lean](src/substitution.lean) - contains basic formalization and proof of correctness of different substitution ciphers

- [stream.lean](src/stream.lean) - contains basic formalization and proof of correctness of stream ciphers

- [block.lean](src/block.lean) - contains basic formalization and proof of correctness of block ciphers

- [feistel.lean](src/feistel.lean) - Proof of correctness for feitsel ciphers

- [dlp.lean](src/dlp.lean) - Formalization of the discrete logarithm problem

- [galois.lean](src/galois.lean) - Bitwise arithmetic in GF(2^n)

- [otp.lean](src/otp.lean) - One-Time Pad correctness

- [lfsr.lean](src/lfsr.lean) - Implement a very basic Linear-Feedback Shift Register that can be used as a random number generator. 

- [modes.lean](src/modes.lean) - Formalize some modes of operations for block ciphers.

- [salsa20/](src/salsa20/) - Attempt to formalize salsa20 from the spec. WORK HAS MOVED TO https://github.com/oxarbitrage/salsa20/
