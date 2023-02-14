/-
 -----------------------------------------------------------
  The computational Diffie-Hellman assumption as a security game
 -----------------------------------------------------------
-/

import measure_theory.probability_mass_function 
import to_mathlib
import uniform

noncomputable theory 

section CDH

variables (G : Type) [fintype G] [group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          -- check Mario, 0 < q necessary for fintype.card?
          (A : G → G → pmf (zmod q))

include g_gen_G G_card_q

def CDH : pmf (zmod q) := 
do 
  α ← uniform_zmod q,
  β ← uniform_zmod q,
  let ω := g^(α.val * β.val),  
  ω' ← A (g^α.val) (g^β.val),
  pure ω'

-- CDHadv[A] is the probability that ω = ω'
local notation `CDHadv[A]` := (CDH G g g_gen_G q G_card_q A 1 : ℝ)

#check CDH G g g_gen_G q G_card_q A 

def DDH (ε : nnreal) : Prop := abs (Pr[DDH0(D)] - Pr[DDH1(D)]) ≤ ε

end CDH
