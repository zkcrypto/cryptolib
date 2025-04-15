/-
Copyright (c) 2023 Ashley Blacquiere
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Ashley Blacquiere
-/
import Cryptolib.ToMathlib
import Cryptolib.Uniform
import Mathlib.Probability.Distributions.Uniform

/-!
# The computational Diffie-Hellman assumption as a security game
-/

noncomputable section

section CDH

variable (G : Type) [Fintype G] [Group G]
         (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [NeZero q] (G_card_q : Fintype.card G = q)
         (A : G → G → PMF G)

include g_gen_G G_card_q -- assumptions used in the game reduction

def CDH : PMF (ZMod 2) :=
do
  let α ← uniform_zmod q
  let β ← uniform_zmod q
  let ω := g^(α.val * β.val)
  let ω' ← A (g^α.val) (g^β.val)
  pure (if ω = ω' then 1 else 0) -- ??

-- CDHadv[A] is the probability that ω = ω'
-- Should CDH be a Prop? Not sure how to get both ω and ω' out to compare outside of the def
local notation "CDHadv[A]" => (CDH G g g_gen_G q G_card_q A)

#check CDH G g /- g_gen_G -/ q /- G_card_q -/ A

end CDH
