/-
  Section 3 : The quarterround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words

open words

namespace quarterround

-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7)
def z₁ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 1) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (y.nth 0) (y.nth 3)))) 7)

-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9)
def z₂ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 2) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z₁ y) (y.nth 0)))) 9)

-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13)
def z₃ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 3) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z₂ y) (z₁ y)))) 13)

-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18)
def z₀ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 0) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z₃ y) (z₂ y)))) 18)

-- quarterround(y = y₀, y₁, y₂, y₃) = (z₀, z₁, z₂, z₃)
def quarterround (y : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 :=
    subtype.mk [z₀ y, z₁ y, z₂ y, z₃ y] (by refl)

-- quarterround(0, 0, 0, 0) = [0, 0, 0, 0]
lemma quarterround_zero : 
  (quarterround (subtype.mk [0, 0, 0, 0] (by refl))).to_list = [0, 0, 0, 0] := rfl

-- TODO: The whole quarterround function is invertible
def quarterround_inv (z : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 :=
  do 
    sorry

end quarterround
