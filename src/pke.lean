/-
 -----------------------------------------------------------
  Security games as pmfs 
 -----------------------------------------------------------
-/

import data.zmod.basic
import measure_theory.probability_mass_function
import to_mathlib
import uniform

noncomputable theory 

/-
  G1 = public key space, G2 = private key space, 
  M = message space, C = ciphertext space 
  A_state = type for state A1 passes to A2
-/
variables {G1 G2 M C A_state: Type} [decidable_eq M]
          (keygen : pmf (G1 × G2))
          (encrypt : G1 → M → pmf C)
          (decrypt : G2 → C → M)
          (A1 : G1 → pmf (M × M × A_state))
          (A2 : C → A_state → pmf (zmod 2)) -- Should have G1 else how can A2 do further encryptions? Any general result about encryptions before getting challenge ciphertext...?

/- 
  Executes the a public-key protocol defined by keygen,
  encrypt, and decrypt
-/
-- Simulates running the program and returns 1 with prob 1 if:
-- `Pr[D(sk, E(pk, m)) = m] = 1` holds
def enc_dec  (m : M) : pmf (zmod 2) :=  -- given a message m
do 
  k ← keygen, -- produces a public / secret key pair
  c ← encrypt k.1 m, -- encrypts m using pk
  pure (if decrypt k.2 c = m then 1 else 0) -- decrypts using sk and checks for equality with m

#check enc_dec

/- 
  A public-key encryption protocol is correct if decryption undoes 
  encryption with probability 1
-/

def pke_correctness : Prop := ∀ (m : M), enc_dec keygen encrypt decrypt m = pure 1 -- This chain of encryption/decryption matches the monadic actions in the `enc_dec` function

#check pke_correctness
#check pke_correctness keygen
/- 
  The semantic security game. 
  Returns 1 if the attacker A2 guesses the correct bit
-/
def SSG : pmf (zmod 2):= 
do 
  k ← keygen, 
  m ← A1 k.1, 
  b ← uniform_2,
  c ← encrypt k.1 (if b = 0 then m.1 else m.2.1),
  b' ← A2 c m.2.2,
  pure (1 + b + b')

-- SSG(A) denotes the event that A wins the semantic security game
local notation `Pr[SSG(A)]` := (SSG keygen encrypt A1 A2 1 : ℝ)

def pke_semantic_security (ε : nnreal) : Prop := abs (Pr[SSG(A)] - 1/2) ≤ ε 

#check Pr[SSG(A)]