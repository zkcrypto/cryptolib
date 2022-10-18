/-
  Section 6 : The doubleround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.rowround
import salsa20.columnround

open words
open rowround
open columnround

namespace doubleround

-- A double round is a column round followed by a row round: doubleround(x) =
-- rowround(columnround(x))
def doubleround(x : vector (bitvec word_len) 16) : vector (bitvec word_len) 16 := do
  let cr := columnround x,
  let y₀ := cr.nth 0,
  let y₁ := cr.nth 1,
  let y₂ := cr.nth 2,
  let y₃ := cr.nth 3,
  let y₄ := cr.nth 4,
  let y₅ := cr.nth 5,
  let y₆ := cr.nth 6,
  let y₇ := cr.nth 7,
  let y₈ := cr.nth 8,
  let y₉ := cr.nth 9,
  let y₁₀ := cr.nth 10,
  let y₁₁ := cr.nth 11,
  let y₁₂ := cr.nth 12,
  let y₁₃ := cr.nth 13,
  let y₁₄ := cr.nth 14,
  let y₁₅ := cr.nth 15,

  rowround ([y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16)

lemma doubleround_zero : 
  doubleround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

end doubleround
