/-
  Section 7 : The littleendian function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words

-- Inputs and outputs:
-- If b is a 4-byte sequence then littleendian(b) is a word.

-- If b = (b0, b1, b2, b3) then 
-- littleendian(b) = b0 + (2^8)*b1 + (2^16)*b2 + (2^24)*b3
def littleendian (b : vector (bitvec byte_len) 4) : bitvec word_len := 
  bitvec.of_nat word_len (
    (b.nth 0).to_nat + 
    ((2^8) * (b.nth 1).to_nat) + 
    ((2^16) * (b.nth 2).to_nat) + 
    ((2^24) * (b.nth 3).to_nat))

#check littleendian

#eval (littleendian ([0, 0, 0, 0].to_vec_of_bitvec byte_len 4)).to_nat
#eval 0x00000000

lemma littleendian_zero : 
  (littleendian ([0, 0, 0, 0].to_vec_of_bitvec byte_len 4)).to_nat = 0 
  := rfl

#eval bitvec.to_nat (littleendian ([86, 75, 30, 9].to_vec_of_bitvec byte_len 4))
#eval 0x091e4b56

#eval bitvec.to_nat (littleendian ([255, 255, 255, 250].to_vec_of_bitvec byte_len 4))
#eval 0xfaffffff

#eval bitvec.to_nat (littleendian ([255, 255, 255, 255].to_vec_of_bitvec byte_len 4))
#eval 0xffffffff

-- https://crypto.stackexchange.com/a/22314
def littleendian_inv (w : bitvec word_len) : vector (bitvec byte_len) 4 :=
  [
    bitvec.of_nat byte_len (bitvec.to_nat((bitvec.and w 0xff))),
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 8).and 0xff))),
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 16).and 0xff))), 
    bitvec.of_nat byte_len (bitvec.to_nat(((bitvec.ushr w 24).and 0xff)))
  ].to_vec_of_bitvec byte_len 4

#eval (littleendian_inv 0x00000000).to_list

#eval 0x091e4b56
#eval (littleendian_inv 0x091e4b56).to_list
#eval ((littleendian_inv 0x091e4b56).nth 0).to_nat
#eval ((littleendian_inv 0x091e4b56).nth 1).to_nat
#eval ((littleendian_inv 0x091e4b56).nth 2).to_nat
#eval ((littleendian_inv 0x091e4b56).nth 3).to_nat

#eval (littleendian_inv 0xfaffffff).to_list

lemma inv_undoes_littleendian (b0 b1 b2 b3 : bitvec byte_len) : 
  (littleendian_inv (littleendian ([b0, b1, b2, b3].to_vec_of_bitvec byte_len 4))).to_list = 
    [b0, b1, b2, b3] :=
begin
  sorry,
end
