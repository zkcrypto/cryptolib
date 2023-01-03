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
-/
variables {G M R C A_state : Type} [decidable_eq M]
          (gen : pmf G)
          (commit : G → M → pmf C)
          (verify : G → C → M)
          (A1 : G → pmf (M × M × A_state)) -- Rewrite
          (A2 : C → A_state → pmf (zmod 2)) -- Rewrite

/- 
  Executes commitment protocol defined by opening_value, commit and verify
-/
-- Simulates running the program and returns 1 with prob 1 if:
-- `Verify(c, m, d)` holds
def commit_verify (m : M) : pmf (zmod 2) := 
do 
  h ← gen, -- Not needed? h isn't typical of all commitment schemes - gen should generate G, g, q, and h in the case of Pedersen and elgamal
  d ← gen, -- But this should be chosen uniformly from ℤq
  c ← commit h m, -- c would be some (G x ℤq) - opening value as part of commit
  pure (if verify h c = m then 1 else 0) 

/- 
  A commitment protocol is correct if verification undoes 
  commitment with probability 1
-/

def commitment_correctness : Prop := ∀ (m : M), commit_verify gen commit verify m = pure 1 

#check commitment_correctness


/- 
  A commitment scheme must obey two properties
  Hiding: "commitment c does not leak information about m (either perfect secrecy, or computational indistinguishability)"
  Binding: "no adversary (either powerful or computationally bounded) can generate c, m 6 = m′ and d, d′ such that both Verify(c, m, d) and Verify(c, m′, d′) accept"
-/


def hiding_prop : Prop := sorry -- Note can't use 'hiding' for some reason - namespace collision?
def binding_prop : Prop := sorry



/- 
  The hiding game. 
  Returns 1 if the attacker A2 guesses the correct bit

  In regards to security properties: Have to be defined in terms of the first step of the protocol which returns the commitment, but not (M x d)
-/
def HG : pmf (zmod 2):= 
do 
  -- k ← keygen,  -- No need for this
  m ← A1 k.1, -- A1 outputs M
  b ← uniform_2, -- adversary only gets first component of pair
  c ← encrypt k.1 (if b = 0 then m.1 else m.2.1),
  b' ← A2 c m.2.2,
  pure (1 + b + b')

-- SSG(A) denotes the event that A wins the semantic security game
local notation `Pr[HG(A)]` := (HG keygen encrypt A1 A2 1 : ℝ) -- Rewrite

def hiding_property (ε : nnreal) : Prop := abs (Pr[HG(A)] - 1/2) ≤ ε 
-- Also need perfect hiding
