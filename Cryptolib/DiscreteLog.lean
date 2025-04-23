/-
Copyright (c) 2023 Ashley Blacquiere
Released under either MIT or Apache 2.0 as described in the file README.md.
Authors: Ashley Blacquiere
-/
import Cryptolib.ToMathlib
import Cryptolib.Uniform
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Distributions.Uniform

noncomputable section

section DL

variable (G : Type) [Fintype G] [Group G] [DecidableEq G]
         (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [NeZero q] (G_card_q : Fintype.card G = q)
         (A : G → PMF (ZMod q))

include g_gen_G G_card_q -- assumptions used in the game reduction

  -- let α ← uniform_zmod q
  -- let u := g^α.val
  -- let α' ←  A u

def DL /- (h : G) -/ : PMF (ZMod 2) :=
do
  let α ← uniform_zmod q
  let u := g^α.val
  let α' ←  A u
  pure (if α = α' then 1 else 0)

-- -- From DDH:
-- -- DDH0(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^(xy))
-- local notation "Pr[DDH0(D)]" => (DDH0 G g g_gen_G q G_card_q D 1)

-- -- DDH1(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^z)
-- local notation "Pr[DDH1(D)]" => (DDH1 G g g_gen_G q G_card_q D 1)

local notation "Pr[DL(A)]" => (DL G g /- g_gen_G -/ q /- G_card_q -/ A 1)

def DLadv (ε: NNReal) : Prop := abs (Pr[DL(A)].toReal - 1/2) ≤ ε


#check DL G g /- g_gen_G -/ q /- G_card_q -/ A

end DL
