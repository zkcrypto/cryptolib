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
  C = commitment space (in theory includes committed message and opening value computed by committer)
-/

/-
Commitment phase:
1. Run Gen to establish public security parameters (R to run?).
2. C samples an opening value, computes commitment, and sends commitment to R.

Verification phase:
3. C sends message, opening value pair to R.
4. R accepts or rejects commitment depending on result of verification.
-/

/-
From Boneh & Shoup:
A security parameter (λ) and system parameter (Λ) are used to index families of key spaces, message spaces and ciphertext spaces. 
-/

variables {G M D C : Type}
          (gen : G) -- generates the public parameter, h ∈ G
          (commit : M → pmf (C × D) ) -- C must be pmf to match monadic expectations in `commit_verify`
          (verify : C → D → M → bool)

          (BindingAdversary : pmf (C × D × D × M × M)) 
          (HidingAdversary : pmf (M × M))
          (A : (C × D) → zmod 2)

/-
Simulates running the program and returns 1 with prob 1 if verify holds
`d : D` is passed in rather than generate by the commiter
-/
def commit_verify (m : M) (d : D) : pmf (zmod 2) := 
do 
  c ← commit m, 
  pure (if verify c.1 c.2 m then 1 else 0) 

/- 
  A commitment protocol is correct if verification undoes 
  commitment with probability 1
-/
def commitment_correctness : Prop := ∀ (m : M) (d : D), commit_verify commit verify m d = pure 1 

/-
  Binding: "no adversary (either powerful or computationally bounded) can generate c, m = m' and d, d' such that both Verify(c, m, d) and Verify(c, m', d') accept"
-/
def BG : pmf (zmod 2) :=
do 
  bc ← BindingAdversary,
  pure (if verify bc.1 bc.2.1 bc.2.2.2.1 = verify bc.1 bc.2.2.1 bc.2.2.2.2 then 0 else 1) -- reverse if-else result since we want the negation

local notation `Pr[BG(A)]` := (BG verify BindingAdversary 1 : ℝ) -- #check BG seems reversed?

def binding_property (ε : nnreal) : Prop := abs (Pr[BG(A)] - 1/2) ≤ ε

/- 
  Hiding: "commitment c does not leak information about m (either perfect secrecy, or computational indistinguishability)"
-/

def HG (d : D) : pmf (zmod 2):= 
do 
  hc ← HidingAdversary,
  b ← uniform_2,
  c ← commit hc.1,
  let b' := A c,
  pure (if b = b' 1 else 0)

local notation `Pr[HG(A)]` := (HG verify HidingAdversary 1 : ℝ) 

def hiding_property (ε : nnreal) : Prop := abs (Pr[HG(A)] - 1/2) ≤ ε

-- game where adv. generates two messages
-- commiter commits to one chosen at random
-- opening value has to be an input to commit, but we don't really care what it is (could be a series of coin flips in the process or, could be a random string provided as input) 


-- Also need perfect hiding
-- Definition of perfect binding...? Has anyone written this down?