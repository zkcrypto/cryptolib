
import dlog
import commitments


section pedersen

noncomputable theory 

variables {M : Type}
          (G : Type) [fintype G] [group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          (A : G → pmf G)

include g_gen_G G_card_q -- assumptions used in the game reduction

-- parameters (A1 : G → pmf (G × G × A_state))
--            (A2 : G → G → A_state → pmf (zmod 2))

-- randomly generates a public h ∈ G
def gen : pmf G := 
do 
  x ← uniform_zmod q,
  pure (g^x.val) 

def commit (m : M) (h : G) : pmf (G × zmod q) := 
do
  y ← uniform_zmod q,
  pure (g^m * h^y.val, y)


/- 
  The probability of the binding adversary winning the security game (i.e. finding messages, m and m', and opening values, o and o', such that they both resolve to the same commitment c), is equal to the probability of A winning the game DL. 
-/
-- theorem BG_DL : BG (binding adversary, verify) =  DL ?? :=
-- begin
--   sorry,
-- end


end pedersen
