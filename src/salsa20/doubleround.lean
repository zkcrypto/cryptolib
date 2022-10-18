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
  let y := columnround x,
  rowround y

lemma doubleround_zero : 
  doubleround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

end doubleround
