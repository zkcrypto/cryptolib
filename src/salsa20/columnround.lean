/-
  Section 5 : The columnrow function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.quarterround

open words
open quarterround

namespace columnround

-- (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
def columnround1 (x₀ x₄ x₈ x₁₂ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₀, x₄, x₈, x₁₂].to_vec_of_bitvec word_len 4)

-- (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
def columnround2 (x₅ x₉ x₁₃ x₁ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₅, x₉, x₁₃, x₁].to_vec_of_bitvec word_len 4)

-- (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
def columnround3 (x₁₀ x₁₄ x₂ x₆ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₁₀, x₁₄, x₂, x₆].to_vec_of_bitvec word_len 4)

-- (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
def columnround4 (x₁₅ x₃ x₇ x₁₁ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₁₅, x₃, x₇, x₁₁].to_vec_of_bitvec word_len 4)

-- If x = (x₀, x₁, x₂, x₃, ... , x₁₅) then 
-- columnround(x) = (y₀, y₁, y₂, y₃, ... , y₁₅) where
-- (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
-- (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
-- (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
-- (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
def columnround
  (x : vector (bitvec word_len) 16) : vector (bitvec word_len) 16 :=
  do
    let c1 := columnround1 (x.nth 0) (x.nth 4) (x.nth 8) (x.nth 12),
    let c2 := columnround2 (x.nth 5) (x.nth 9) (x.nth 13) (x.nth 1),
    let c3 := columnround3 (x.nth 10) (x.nth 14) (x.nth 2) (x.nth 6),
    let c4 := columnround4 (x.nth 15) (x.nth 3) (x.nth 7) (x.nth 11),

    let y₀ := c1.head,
    let y₄ := c1.nth 1,
    let y₈ := c1.nth 2,
    let y₁₂ := c1.nth 3,

    let y₅ := c2.head,
    let y₉ := c2.nth 1,
    let y₁₃ := c2.nth 2,
    let y₁ := c2.nth 3,

    let y₁₀ := c3.head,
    let y₁₄ := c3.nth 1,
    let y₂ := c3.nth 2,
    let y₆ := c3.nth 3,

    let y₁₅ := c4.head,
    let y₃ := c4.nth 1,
    let y₇ := c4.nth 2,
    let y₁₁ := c4.nth 3,

    [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16

lemma columnround_zero : 
  columnround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

-- TODO: equivalent formula
-- TODO: matrix form

end columnround
