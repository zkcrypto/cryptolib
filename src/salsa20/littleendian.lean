/-
  Section 7 : The littleendian function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
open words

namespace littleendian

-- Inputs and outputs:
-- If b is a 4-byte sequence then littleendian(b) is a word.

-- If b = (b₀, b₁, b₂, b₃) then 
-- littleendian(b) = b₀ + (2^8)*b₁ + (2^16)*b₂ + (2^24)*b₃
def littleendian (b : vector (bitvec byte_len) 4) : bitvec word_len := 
  bitvec.of_nat word_len (
    (b.nth 0).to_nat +  ((2^8) * (b.nth 1).to_nat) + ((2^16) * (b.nth 2).to_nat) + ((2^24) * (b.nth 3).to_nat)
  )

lemma littleendian_zero :
  (littleendian (subtype.mk [0, 0, 0, 0] (by refl))).to_nat = 0 := rfl

-- The inverse of little-endian is indeed the function that sends a word (32 bits) 
-- back to the sequence of 4 bytes in a little endian way, so the least significant
-- byte goes first, and the most significant byte goes last. 
-- So it maps 𝑤 to w & 0xff, (w >> 8) & 0xff, (w >> 16) & 0xff, (w >> 24) & 0xff
--
-- https://crypto.stackexchange.com/a/22314
def littleendian_inv (w : bitvec word_len) : vector (bitvec byte_len) 4 :=
  subtype.mk [
    bitvec.of_nat byte_len (bitvec.to_nat((bitvec.and w 0xff))),
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 8).and 0xff))),
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 16).and 0xff))), 
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 24).and 0xff)))
  ] (by refl)

lemma littleendian_inv_zero :
  littleendian_inv 0 = (subtype.mk [0, 0, 0, 0] (by refl)) := rfl


lemma inv_undoes_littleendian (b : vector (bitvec byte_len) 4) : littleendian_inv (littleendian b) = b :=
begin
  sorry,
end

end littleendian
