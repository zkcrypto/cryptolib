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
  quarterround ([y₀, y₁, y₂, y₃].to_vec_of_bitvec word_len 4)

-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
def rowround2 (y₅ y₆ y₇ y₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₅, y₆, y₇, y₄].to_vec_of_bitvec word_len 4)

-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
def rowround3 (y₁₀ y₁₁ y₈ y₉ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₁₀, y₁₁, y₈, y₉].to_vec_of_bitvec word_len 4)

-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround4 (y₁₅ y₁₂ y₁₃ y₁₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₁₅, y₁₂, y₁₃, y₁₄].to_vec_of_bitvec word_len 4)

-- If y = (y₀, y₁, y₂, y₃, ... , y₁₅) then 
-- rowround(y) = (z₀, z₁, z₂, z₃, ... , z₁₅) where
-- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround (y : vector(bitvec word_len) 16) : vector (bitvec word_len) 16 :=
  do
    let list1 := rowround1 (y.nth 0) (y.nth 1) (y.nth 2) (y.nth 3),
    let list2 := rowround2 (y.nth 5) (y.nth 6) (y.nth 7) (y.nth 4),
    let list3 := rowround3 (y.nth 10) (y.nth 11) (y.nth 8) (y.nth 9),
    let list4 := rowround4 (y.nth 15) (y.nth 12) (y.nth 13) (y.nth 14),

    let z₅ := list2.head,
    let z₆ := list2.nth 1,
    let z₇ := list2.nth 2,
    let z₄ := list2.nth 3,

    let list2_sorted := [z₄, z₅, z₆, z₇].to_vec_of_bitvec word_len 4, 

    let z₁₀ := list3.head,
    let z₁₁ := list3.nth 1,
    let z₈ := list3.nth 2,
    let z₉ := list3.nth 3,

    let list3_sorted := [z₈, z₉, z₁₀, z₁₁].to_vec_of_bitvec word_len 4,

    let z₁₅ := list4.head,
    let z₁₂ := list4.nth 1,
    let z₁₃ := list4.nth 2,
    let z₁₄ := list4.nth 3,

    let list4_sorted := [z₁₂, z₁₃, z₁₄, z₁₅].to_vec_of_bitvec word_len 4,
    
    ((list1.append list2_sorted).append list3_sorted).append list4_sorted

lemma rowround_zero : 
  rowround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

-- TODO: matrix form

end rowround