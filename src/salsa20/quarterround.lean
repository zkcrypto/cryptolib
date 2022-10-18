/-
  Section 3 : The quarterround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words

open words

namespace quarterround

-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7)
def z₁ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 1) (rotate7 (nat_as_bitvec (mod_as_nat (sum_as_mod (y.nth 0) (y.nth 3)))))

-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9)
def z₂ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 2) (rotate9 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₁ y) (y.nth 0)))))

-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13)
def z₃ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 3) (rotate13 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₂ y) (z₁ y)))))

-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18)
def z₀ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 0) (rotate18 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₃ y) (z₂ y)))))

-- quarterround(y = y0, y1, y2, y3) = (z0, z1, z2, z3)
def quarterround (y : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 :=
    [z₀ y, z₁ y, z₂ y, z₃ y].to_vec_of_bitvec word_len 4

-- quarterround(0, 0, 0, 0) = [0, 0, 0, 0]
lemma quarterround_zero : 
  (quarterround ([0, 0, 0, 0].to_vec_of_bitvec word_len 4)).to_list = [0, 0, 0, 0] := rfl

-- TODO: The whole quarterround function is invertible
def quarterround_inv : list (bitvec word_len) :=
  do 
    sorry

end quarterround
