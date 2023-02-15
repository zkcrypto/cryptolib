import measure_theory.probability_mass_function 
import uniform

noncomputable theory 

section DL

variables (G : Type) [fintype G] [group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          (A : G → pmf G)

include g_gen_G G_card_q -- assumptions used in the game reduction

def DL : pmf G := 
do 
  α ← uniform_zmod q,
  let u := g^α.val,
  α' ←  A u,
  pure α'

-- -- From DDH:
-- -- DDH0(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^(xy))
-- local notation `Pr[DDH0(D)]` := (DDH0 G g g_gen_G q G_card_q D 1 : ℝ)

-- -- DDH1(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^z)
-- local notation `Pr[DDH1(D)]` := (DDH1 G g g_gen_G q G_card_q D 1 : ℝ)


def DLadv : Prop := sorry


#check DL G g g_gen_G q G_card_q A 

end DL