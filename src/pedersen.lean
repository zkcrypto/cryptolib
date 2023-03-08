
import dlog
import commitments


section pedersen

noncomputable theory 

variables {M : Type}
          (G : Type) [fintype G] [group G] [decidable_eq G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g) 
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          (A : G → pmf G)

include g_gen_G G_card_q -- assumptions used in the game reduction

-- parameters (A1 : G → pmf (G × G × A_state))
--            (A2 : G → G → A_state → pmf (zmod 2))

/-
To implement:
(gen : pmf G) -- generates the public parameter, h ∈ G
(commit : G → M → pmf (C × D) )
(verify : G → C → D → M → bool)
(BindingAdversary : G → pmf (C × D × D × M × M)) 
-/

-- (gen : pmf G) -- generates the public parameter, h ∈ G
def gen : pmf G := 
do 
  x ← uniform_zmod q,
  pure (g^x.val) 

-- commit : G → M → pmf (C × D)
def commit (h : G) (m : zmod q) : pmf (G × zmod q) := 
do
  y ← uniform_zmod q,
  pure (g^m.val * h^y.val, y)
 
-- verify : G → C → D → M → bool
def verify (h : G) (c : G) (d : zmod q) (m : zmod q) : Prop :=
do 
  -- let c' := commit h m, 
  let c' := g^m.val * h^d.val,
  pure (if c' = c then 1 else 0) -- G isn't decidable?

-- BindingAdversary : G → pmf (C × D × D × M × M)
def BindingAdversary (h : G) : pmf (G × zmod q × zmod q × M × M) :=
do

/- 
  The probability of the binding adversary winning the security game (i.e. finding messages, m and m', and opening values, o and o', such that they both resolve to the same commitment c), is equal to the probability of A winning the game DL. 
-/

#check BG
theorem BG_DL : BG gen verify BindingAdversary  =  DL ?? :=
begin
  sorry,
end


end pedersen
