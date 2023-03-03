/-
 ---------------------------------------------------------------
  The computational Diffie-Hellman assumption as a security game
 ---------------------------------------------------------------
-/

import measure_theory.probability_mass_function 
import to_mathlib
import uniform

noncomputable theory 

section CDH

variables (G : Type) [fintype G] [group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          (A : G → G → pmf G)

include g_gen_G G_card_q -- assumptions used in the game reduction 

def CDH : pmf (zmod 2) := 
do 
  α ← uniform_zmod q,
  β ← uniform_zmod q,
  let ω := g^(α.val * β.val),  
  ω' ← A (g^α.val) (g^β.val),
  pure (if ω = ω' then 1 else 0) -- ??

-- CDHadv[A] is the probability that ω = ω'
-- Should CDH be a Prop? Not sure how to get both ω and ω' out to compare outside of the def
local notation `CDHadv[A]` := (CDH G g g_gen_G q G_card_q A)

#check CDH G g g_gen_G q G_card_q A 

end CDH