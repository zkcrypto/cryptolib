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
          (commit : M → D → C) -- send c.1 - don't send the opening value - it doesn't to be remenbered, only in the binding experiment do we need two values quantified overall messages
          (verify : C → M → D → bool)

          (Adversary1 : pmf (C × Commiter_state)) -- phase 1 M x X
          (Adversary2 : Commiter_state → (M × D)) -- phase 2 commiter

/-
Simulates running the program and returns 1 with prob 1 if verify holds
-/
def commit_verify (m : M) (d : D) : pmf (zmod 2) := 
do 
  c ← commit m d, 
  pure (if verify c m d then 1 else 0) 

/- 
  A commitment protocol is correct if verification undoes 
  commitment with probability 1
-/
def commitment_correctness : Prop := ∀ (m : M) (d : D), commit_verify commit verify m = pure 1 

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
  m ← Commiter1 k.1, -- A1 outputs M
  b ← uniform_2, -- adversary only gets first component of pair
  c ← encrypt k.1 (if b = 0 then m.1 else m.2.1),
  b' ← A2 c m.2.2,
  pure (1 + b + b')

def hiding_property (ε : nnreal) : Prop := abs (Pr[HG(A)] - 1/2) ≤ ε 

-- game where adv. generates two messages
-- commiter commits to one chosen at random
-- opening value has to be an input to commit, but we don't really care what it is (could be a series of coin flips in the process or, could be a random string provided as input) 


-- Also need perfect hiding
-- Definition of perfect binding...? Has anyone written this down?