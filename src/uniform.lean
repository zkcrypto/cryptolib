/-
 -----------------------------------------------------------
  Uniform distributions over zmod q, bitvecs, and finite groups
 -----------------------------------------------------------
-/

import to_mathlib
import probability.probability_mass_function.uniform

variables (G : Type) [fintype G] [group G] [decidable_eq G]

noncomputable theory 

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.uniform_of_fintype (bitvec n)

def uniform_grp : pmf G := 
    pmf.uniform_of_fintype G
 
variable (g : G)
#check (uniform_grp G)
def uniform_zmod (n : ℕ) [ne_zero n] : pmf (zmod n) := uniform_grp (zmod n) -- replaced [fact (0 < n)] with [ne_zero n] and line 52 below

def uniform_2 : pmf (zmod 2) := uniform_zmod 2 

lemma uniform_grp_prob : 
  ∀ (g : G), (uniform_grp G) g = 1 / fintype.card G := 
begin
  intro g,
  rw [uniform_grp, pmf.uniform_of_fintype_apply, inv_eq_one_div],
end 

lemma uniform_zmod_prob {n : ℕ} [ne_zero n] :
  ∀ (a : zmod n), (uniform_zmod n) a = 1/n := 
begin
  intro a,
  rw [uniform_zmod, uniform_grp, pmf.uniform_of_fintype_apply],
  simp,
end
