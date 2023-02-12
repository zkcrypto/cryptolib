# Crypto formal proofs meeting

## Jan. 25, 2023

### Questions
- Is the definition on pg. 339 of Boneh and Shoup the best foundation for binding and hiding?
- Statistical = Perfect = Unconditional hiding / binding?
- Why are the schemes on pg. 341 of Boneh and Shoup computationally binding and unconditionally hiding? What sets this scheme apart from the scheme on pg. 336 and pg. 87?
- Can we draw something like figure 2.6 (pg. 35) for our specific purposes?

### Notes
- Lupo treats all protocol components as parameters
- h in Pedersen would have to come from a set up
    - Binding game - first step is setup function:
        - Generates h
        - Adv gets h
        - Adv generates (M x M)
        - Both evaluate to C
        - => DLOG game 

- In DLOG - given challenge respond with challenge
- Query - Lupo's framework won't handle this because it's specific case
- More complex proof need some additional machinery
- Hart: Has not seen automated proofs of interactive reduction proofs
- Goldriech-Levin - automated proof? - Simplest case of an interactive reduction