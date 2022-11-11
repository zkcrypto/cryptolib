/-
  Section 4 : The rowround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import data.matrix.basic

import salsa20.words
import salsa20.quarterround

open matrix

open words
open quarterround

namespace rowround

-- Given a vector of 16 words, convert it to a 4x4 matrix.
def vector_as_matrix (y : vector(bitvec word_len) 16) : matrix (fin 4) (fin 4) (bitvec word_len) :=
  ![
    ![(y.nth 0), (y.nth 1), (y.nth 2), (y.nth 3)],
    ![(y.nth 4), (y.nth 5), (y.nth 6), (y.nth 7)],
    ![(y.nth 8), (y.nth 9), (y.nth 10), (y.nth 11)],
    ![(y.nth 12), (y.nth 13), (y.nth 14), (y.nth 15)]
  ]

-- The rowround function in the matrix form
def rowround (y : vector(bitvec word_len) 16) : matrix (fin 4) (fin 4) (bitvec word_len) := do
  let Y := vector_as_matrix y,

  -- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
  let row1 := quarterround (subtype.mk [(Y 0 0), (Y 0 1), (Y 0 2), (Y 0 3)] (by refl)),
  -- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
  let row2 := quarterround (subtype.mk [(Y 1 1), (Y 1 2), (Y 1 3), (Y 1 0)] (by refl)),
  -- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
  let row3 := quarterround (subtype.mk [(Y 2 2), (Y 2 3), (Y 2 0), (Y 2 1)] (by refl)),
  -- quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
  let row4 := quarterround (subtype.mk [(Y 3 3), (Y 3 0), (Y 3 1), (Y 3 2)] (by refl)),

  let new_matrix := 
  ![
    ![(row1.nth 0), (row1.nth 1), (row1.nth 2), (row1.nth 3)],
    ![(row2.nth 3), (row2.nth 0), (row2.nth 1), (row2.nth 2)],
    ![(row3.nth 2), (row3.nth 3), (row3.nth 0), (row3.nth 1)],
    ![(row4.nth 1), (row4.nth 2), (row4.nth 3), (row4.nth 0)]
  ],

  new_matrix

-- The rowround of input all zeros is a matrix where its componenets are all zeros.
lemma rowround_zero :
  rowround (subtype.mk [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by refl)) = 
    ![
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0]
    ] := rfl


end rowround
