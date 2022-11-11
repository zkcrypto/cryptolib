/-
  Section 5 : The columnrow function
  http://cr.yp.to/snuffle/spec.pdf
-/
import data.matrix.basic

import salsa20.words
import salsa20.quarterround
import salsa20.rowround

open words
open quarterround
open rowround

namespace columnround

-- Given a 4x4 matrix convert it to a vector of 16 word bitvects.
def matrix_as_vector (Y : matrix (fin 4) (fin 4) (bitvec word_len)) : vector (bitvec word_len) 16 :=
  subtype.mk [
    Y 0 0, Y 0 1, Y 0 2, Y 0 3,
    Y 1 0, Y 1 1, Y 1 2, Y 1 3,
    Y 2 0, Y 2 1, Y 2 2, Y 2 3,
    Y 3 0, Y 3 1, Y 3 2, Y 3 3
  ] (by refl)

-- The columnround function defined as the transpose of the rowround
def columnround (y : vector(bitvec word_len) 16) : matrix (fin 4) (fin 4) (bitvec word_len) := do
  -- transpose the input
  let Y := (vector_as_matrix y).transpose,
  -- apply rowround and transpose the result
  (rowround (matrix_as_vector Y)).transpose

-- The columnround of input all zeros is a matrix where its componenets are all zeros.
lemma columnround_zero : 
  columnround (subtype.mk [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by refl)) = 
    ![
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0],
     ![0, 0, 0 ,0]
    ] :=
    begin
      exact dec_trivial,
    end


end columnround
