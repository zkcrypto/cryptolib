/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Cryptolib.ToMathlib
import Cryptolib.Uniform
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Security games as PMFs

This file provides formal definitions for correctness and semantic security of a public
key encryption scheme.
-/

noncomputable section

/-
G1 = public key space, G2 = private key space,
M = message space, C = ciphertext space
A_state = type for state A1 passes to A2
-/
variable {G1 G2 M C A_state: Type} [DecidableEq M]
         (keygen : PMF (G1 × G2))
         (encrypt : G1 → M → PMF C)
         (decrypt : G2 → C → M)
         (A1 : G1 → PMF (M × M × A_state))
         (A2 : C → A_state → PMF (ZMod 2)) -- Should have G1 else how can A2 do further encryptions? Any general result about encryptions before getting challenge ciphertext...?

/-
Executes a public-key protocol defined by keygen,
encrypt, and decrypt
-/
-- Simulates running the program and returns 1 with prob 1 if:
-- `Pr[D(sk, E(pk, m)) = m] = 1` holds
def enc_dec (m : M) : PMF (ZMod 2) :=  -- given a message m
do
  let k ← keygen -- produces a public / secret key pair
  let c ← encrypt k.1 m -- encrypts m using pk
  pure (if decrypt k.2 c = m then 1 else 0) -- decrypts using sk and checks for equality with m

/-
A public-key encryption protocol is correct if decryption undoes
encryption with probability 1
-/

/-
This chain of encryption/decryption matches the monadic actions in the `enc_dec` function
-/
def PkeCorrectness : Prop := ∀ (m : M), enc_dec keygen encrypt decrypt m = pure 1

/-
The semantic security game.
Returns 1 if the attacker A2 guesses the correct bit
-/
def SSG : PMF (ZMod 2) :=
do
  let k ← keygen
  let m ← A1 k.1
  let b ← uniform_2
  let c ← encrypt k.1 (if b = 0 then m.1 else m.2.1)
  let b' ← A2 c m.2.2
  pure (1 + b + b')

-- SSG(A) denotes the event that A wins the semantic security game
local notation "Pr[SSG(A)]" => (SSG keygen encrypt A1 A2 1)

def PkeSemanticSecurity (ε : NNReal) : Prop := abs (Pr[SSG(A)].toReal - 1/2) ≤ ε
