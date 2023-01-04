/-
 -----------------------------------------------------------
  Generic commitments
 -----------------------------------------------------------
-/

import data.zmod.basic
import measure_theory.probability_mass_function
import to_mathlib
import uniform

noncomputable theory 

/-
  G = The agreed upon group (order q and generator g)
  M = message space
  D = space of opening values (order q)
  C = commitment space (in practice includes committed message and opening value computed by S)
  A1 = first
-/

/-
Commitment phase:
1. Run Gen to establish public security parameters (R to run?).
2. C samples an opening value, computes commitment, and sends commitment to R.

Verification phase:
3. C sends message, opening value pair to R.
4. R accepts or rejects commitment depending on result of verification.
-/

variables {G M D C Commiter_state : Type} [decidable_eq M]
          (gen : G → ℤ → G → G) -- Given G, q, g return h
          (commit : M → pmf (C × D))
          (verify : C → M → D → bool)
          (Commiter1 : pmf (C × Commiter_state)) -- phase 1 commiter
          (Commiter2 : Commiter_state → (M × D)) -- phase 2 commiter

/-
Simulates running the program and returns 1 with prob 1 if verify holds
-/
def commit_verify (m : M) : pmf (zmod 2) := 
do 
  c ← commit m, 
  pure (if verify c.1 m c.2 then 1 else 0) 

/- 
  A commitment protocol is correct if verification undoes 
  commitment with probability 1
-/
def commitment_correctness : Prop := ∀ (m : M), commit_verify commit verify m = pure 1 

/- 
  A commitment scheme must obey two properties
  
  Hiding: "commitment c does not leak information about m (either perfect secrecy, or computational indistinguishability)"
  
  Binding: "no adversary (either powerful or computationally bounded) can generate c, m 6 = m′ and d, d′ such that both Verify(c, m, d) and Verify(c, m′, d′) accept"
-/

/- 
  The hiding game. 

  Regarding security properties: Have to be defined in terms of the first step of the protocol which returns the commitment, but not (M x D)
-/
def HG (g : G) (q : ℤ) : pmf (zmod 2):= 
do 
  h ← gen g q g, 
  m ← A1 k.1, -- A1 outputs M
  b ← uniform_2, -- adversary only gets first component of pair
  c ← encrypt k.1 (if b = 0 then m.1 else m.2.1),
  b' ← A2 c m.2.2,
  pure (1 + b + b')

def hiding_property (ε : nnreal) : Prop := abs (Pr[HG(A)] - 1/2) ≤ ε 
-- Also need perfect hiding
