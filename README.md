# cryptolib

Cryptolib is a user-maintained library for the [Lean theorem prover](https://leanprover.github.io).

## Status

This library is a work-in-progress merge, port, and refactor of several forks of a Lean 3 project:

- [The original project](https://github.com/JoeyLupo/cryptolib) was a formal proof of correctness and game-based proof of semantic security for the ElGamal public key encryption protocol using the Lean theorem prover. Its implementation drew from Adam Petcher's Foundational Cryptographic Framework (FCF) Coq library at https://github.com/adampetcher/fcf. The master's dissertation which describes the project in more depth can be found [here](https://1drv.ms/b/s!AkAJTM1hbeSD4wcF1T4NYiRG5b_D?e=0Yp8Hx).
- [The first independent fork](https://github.com/oxarbitrage/cryptolib) extended the project to focus on formal proofs of correctness of different ciphers.
- [The second independent fork](https://github.com/ashandoak/cryptolib) appeared to continue the original project in its academic context, adding some additional security notions and proofs.

## Files in cryptolib

- `ddh.lean` - provides a formal specification of the decisional Diffie-Hellman assumption on a finite cyclic group
	
- [elgamal.lean](src/elgamal.lean) - contains the formal specification of the ElGamal public key encryption protocol, and the formal proofs of correctness 

- [pke.lean](src/pke.lean) - provides formal definitions for correctness and semantic security of a public key encryption scheme

- [tactics.lean](src/tactics.lean) - provides the `bindskip` and `bindconst` tactics to help prove equivalences between pmfs

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

## License

All code in the `scratch` and `src` folders is licensed under Apache License, Version 2.0,
along with the following files:

- `Cryptolib/Fundamentals/Negligible.lean`
- `Cryptolib/Fundamentals/Uniform.lean`
- `Cryptolib/ToMathlib.lean`

All other code in this workspace is licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
