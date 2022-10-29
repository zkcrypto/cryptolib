/-
  Section 4 : The rowround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.quarterround

open words
open quarterround

namespace rowround

-- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
def rowround1 (y₀ y₁ y₂ y₃ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround (subtype.mk [y₀, y₁, y₂, y₃] (by refl))

-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
def rowround2 (y₅ y₆ y₇ y₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround (subtype.mk [y₅, y₆, y₇, y₄] (by refl))

-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
def rowround3 (y₁₀ y₁₁ y₈ y₉ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround (subtype.mk [y₁₀, y₁₁, y₈, y₉] (by refl))

-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround4 (y₁₅ y₁₂ y₁₃ y₁₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround (subtype.mk  [y₁₅, y₁₂, y₁₃, y₁₄] (by refl))

-- If y = (y₀, y₁, y₂, y₃, ... , y₁₅) then 
-- rowround(y) = (z₀, z₁, z₂, z₃, ... , z₁₅) where
-- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround (y : vector(bitvec word_len) 16) : vector (bitvec word_len) 16 :=
  do
    let r1 := rowround1 (y.nth 0) (y.nth 1) (y.nth 2) (y.nth 3),
    let r2 := rowround2 (y.nth 5) (y.nth 6) (y.nth 7) (y.nth 4),
    let r3 := rowround3 (y.nth 10) (y.nth 11) (y.nth 8) (y.nth 9),
    let r4 := rowround4 (y.nth 15) (y.nth 12) (y.nth 13) (y.nth 14),

    let z₀ := r1.head,
    let z₁ := r1.nth 1,
    let z₂ := r1.nth 2,
    let z₃ := r1.nth 3,

    let z₅ := r2.head,
    let z₆ := r2.nth 1,
    let z₇ := r2.nth 2,
    let z₄ := r2.nth 3,

    let z₁₀ := r3.head,
    let z₁₁ := r3.nth 1,
    let z₈ := r3.nth 2,
    let z₉ := r3.nth 3,

    let z₁₅ := r4.head,
    let z₁₂ := r4.nth 1,
    let z₁₃ := r4.nth 2,
    let z₁₄ := r4.nth 3,

    subtype.mk [z₀, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈, z₉, z₁₀, z₁₁, z₁₂, z₁₃, z₁₄, z₁₅] (by refl)

lemma rowround_zero : 
  rowround (subtype.mk [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by refl)) = 
    subtype.mk  [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0] (by refl) := rfl

-- TODO: matrix form

end rowround
