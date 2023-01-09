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

variables {M D C : Type} [decidable_eq M]
          (gen : D) 
          (commit : M → D → pmf C) -- C must be pmf to match monadic expectations in `commit_verify`
          (verify : C → D → pmf M)

          (BindingAdversary : pmf (C × D × D)) 
          (HidingAdversary : (M × M))

/-
Simulates running the program and returns 1 with prob 1 if verify holds
-/
def commit_verify (m : M) (d : D) : pmf (zmod 2) := 
do 
  c ← commit m d, 
  pure (if verify c d = m then 1 else 0) 

/- 
  A commitment protocol is correct if verification undoes 
  commitment with probability 1
-/
def commitment_correctness : Prop := ∀ (m : M) (d : D), commit_verify commit verify m d = pure 1 

/-
  Binding: "no adversary (either powerful or computationally bounded) can generate c, m 6 = m′ and d, d′ such that both Verify(c, m, d) and Verify(c, m′, d′) accept"
-/
def BG : pmf (zmod 2) :=
do 
  bc ← BindingAdversary,
  m₀ ← verify bc.1 bc.2.1,
  m₁ ← verify bc.1 bc.2.2,
  pure (if m₀ = m₁ then 0 else 1) -- reverse if-else result since we want the negation

local notation `Pr[BG(A)]` := (BG verify BindingAdversary 1 : ℝ) -- #check BG seems reversed?

def binding_property (ε : nnreal) : Prop := abs (Pr[BG(A)] - 1/2) ≤ ε

/- 
  Hiding: "commitment c does not leak information about m (either perfect secrecy, or computational indistinguishability)"
-/

def HG : pmf (zmod 2):= 
do 
  hm ← HidingAdversary,


-- game where adv. generates two messages
-- commiter commits to one chosen at random
-- opening value has to be an input to commit, but we don't really care what it is (could be a series of coin flips in the process or, could be a random string provided as input) 


-- Also need perfect hiding
-- Definition of perfect binding...? Has anyone written this down?