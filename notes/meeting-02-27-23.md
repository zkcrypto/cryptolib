# Meeting with Bruce

## Feb. 27, 2023
- Think of commitments in the abstract (four types of _data_)
    - Messages and commitments
    - Parameters (i.e. h in Pedersen) and opening values
- Commitment function (takes a message and a parameter) returns a commitment and opening value
    - Consider binding game - adversary produces all necessary data
- Verification function basically runs C, but also takes parameter h
- Binding - to reduce to discrete log we _must_ have `h` in the BINDAdv (contrary to what B&S state in 8.12) (refer to B&S as way it is defined)

-  In the binding game:
    - Game chooses h using gen
    - Gives h to A
    - A outputs five-tuple - conditions met output 1 else 0

- Perfect hiding: for all m0, m1, etc. - equality of two probs

- Output of commit - pmf over commitments
