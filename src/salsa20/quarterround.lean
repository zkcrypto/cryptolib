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

-- The whole quarterround function is invertible because individual vector components are invertible.
-- From z = [z₀, z₁, z₂, z₃] we can get back to [y₀, y₁, y₂, y₃]

-- The interesting thing is that it seems we don't need to apply the inverses of rotl and zmod
-- addition, instead to get yₓ we just replace zₓ in the original formula and compute. 

-- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18)
def y₀ (z : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (z.nth 0) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z.nth 3) (z.nth 2)))) 18) 

-- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13)
def y₃ (z : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (z.nth 3) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z.nth 2) (z.nth 1)))) 13) 

-- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9)
def y₂ (z : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (z.nth 2) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (z.nth 1) (y₀ z)))) 9) 

-- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7)
def y₁ (z : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (z.nth 1) (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod (y₀ z) (y₃ z)))) 7) 

-- The inverse of the quarterround function puts together the above definitions for the 
-- components of y.
def quarterround_inv (z : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 :=
  subtype.mk [
    y₀ z,
    y₁ z,
    y₂ z,
    y₃ z
  ] (by refl)

-- double quarterround is not the inverse
lemma double_quarterround_not_inverse (y : vector (bitvec word_len) 4) : quarterround (quarterround y) ≠ y :=
begin
  sorry,
end

-- quarterround_inv is the inverse
lemma quarterround_inv_is_inverse (y : vector (bitvec word_len) 4) : y = quarterround_inv (quarterround y) :=
begin
  unfold quarterround_inv,
  unfold quarterround,
  sorry,
end


end quarterround
