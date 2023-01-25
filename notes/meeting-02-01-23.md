# Crypto formal proofs meeting
## Jan. 2, 2023

- If everything is a game - maybe overkill?
- Here is the advantage of shallow embedding in a information theoretic sense
- Comparison between Lean and EasyCrypt
- Commitment based on elgamal - computational secrecy and perfect binding (bijective)
- Automated theorem provers with lattices - awkward distributional arguments - noise smoothing steps - are hard
- Better is LHL for automated proof is better?
- Semantically secure scheme (elgamal) - hiding follows, binding is reasoning about exponentiation being one-to-one
- h^r is uniformly distributed; independence argument might be tricky - must be independent of g^m (but this is implicit in Lean?) - should be implicit in DDH assumption in Lupo.
- DSLs for smart contracts that are not Turing complete makes some general proofs tractable
- [Move Programming Language](https://move-book.com/index.html)
- BLS signatures (after elgamal - push the envelop) - thresholdization  
- Comparison between Lean and EasyCrypt? - Theorem proving is hard, let's not make it harder than it needs to be...