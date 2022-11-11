/-
  Section 3 : The quarterround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words

open words

namespace quarterround

-- quarterround returns a vector [a, b ,c, d] where modifications to elements where made.
-- according to https://en.wikipedia.org/wiki/Salsa20 and the spec.
def quarterround (y : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 := do
  -- a = y₀ and then z₀
  let a := y.nth 0,
  -- b = y₁ and then z₁
  let b := y.nth 1,
  -- c = y₂ and then z₂
  let c := y.nth 2,
  -- d = y₃ and then z₃
  let d := y.nth 3,

  -- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7)
  let b := b.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod a d))) 7),
  -- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9)
  let c := c.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod b a))) 9),
  -- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13)
  let d := d.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod c b))) 13),
  -- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18)
  let a := a.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod d c))) 18),

  subtype.mk [a, b, c, d] (by refl)

-- The whole quarterround function is invertible because individual vector components are invertible.
-- From z = [z₀, z₁, z₂, z₃] we can get back to [y₀, y₁, y₂, y₃]
-- 
-- Note: it is interesting that it seems we don't need to apply the inverses of rotl and zmod
-- addition, instead to get yₓ we just replace zₓ in the original formula and compute. 
def quarterround_inv (z : vector(bitvec word_len) 4) : vector (bitvec word_len) 4 := do
  -- a = z₀ and then y₀
  let a := z.nth 0,
  -- b = z₁ and then y₁
  let b := z.nth 1,
  -- c = z₂ and then y₂
  let c := z.nth 2,
  -- d = z₃ and then y₃
  let d := z.nth 3,

  -- y₀ = z₀ ⊕ ((z₃ + z₂) <<< 18)
  let a := a.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod d c))) 18),
  -- y₃ = z₃ ⊕ ((z₂ + z₁) <<< 13)
  let d := d.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod c b))) 13),
  -- y₂ = z₂ ⊕ ((z₁ + y₀) <<< 9)
  let c := c.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod b a))) 9),
  -- y₁ = z₁ ⊕ ((y₀ + y₃) <<< 7)
  let b := b.xor (rotl (nat_as_bitvec (mod_as_nat (add_bitvecs_as_mod a d))) 7),

  subtype.mk [a, b, c, d] (by refl)

-- 
axiom quarterround_inv_is_always_inv : ∀ (y : vector(bitvec word_len) 4), y = quarterround_inv (quarterround y)

-- quarterround([0, 0, 0, 0]) = [0, 0, 0, 0]
lemma quarterround_zero :
  (quarterround (subtype.mk [0, 0, 0, 0] (by refl))).to_list = [0, 0, 0, 0] := rfl

-- The quarteround function is the inverse
lemma quarterround_inv_is_inv (y : vector(bitvec word_len) 4) : y = quarterround_inv (quarterround y) :=
begin
  rw ← quarterround_inv_is_always_inv,
end

-- applying quarterround twice is not the inverse
lemma double_quarteround_is_not_inv (y : vector(bitvec word_len) 4) : y ≠ quarterround (quarterround y) :=
begin
  sorry,
end


end quarterround
