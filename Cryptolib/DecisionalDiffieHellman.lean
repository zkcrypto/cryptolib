/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Cryptolib.ToMathlib
import Cryptolib.Uniform
import Mathlib.Probability.Distributions.Uniform

/-!
# The decisional Diffie-Hellman assumption as a security game

This file provides a formal specification of the decisional Diffie-Hellman assumption on a
finite cyclic group.
-/

noncomputable section

section DDH

variable (G : Type) [Fintype G] [Group G]
         (g : G) --(g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [NeZero q] --(G_card_q : Fintype.card G = q)
         -- check Mario, 0 < q necessary for Fintype.card?
         (D : G → G → G → PMF (ZMod 2))

-- include g_gen_G G_card_q

def DDH0 : PMF (ZMod 2) :=
do
  let x ← uniform_zmod q
  let y ← uniform_zmod q
  let b ← D (g^x.val) (g^y.val) (g^(x.val * y.val))
  pure b

def DDH1 : PMF (ZMod 2) :=
do
  let x ← uniform_zmod q
  let y ← uniform_zmod q
  let z ← uniform_zmod q
  let b ← D (g^x.val) (g^y.val) (g^z.val)
  pure b

-- DDH0(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^(xy))
local notation "Pr[DDH0(D)]" => (DDH0 G g q D 1)

-- DDH1(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^z)
local notation "Pr[DDH1(D)]" => (DDH1 G g q D 1)

def DDH (ε : NNReal) : Prop := abs (Pr[DDH0(D)].toReal - Pr[DDH1(D)].toReal) ≤ ε

end DDH
