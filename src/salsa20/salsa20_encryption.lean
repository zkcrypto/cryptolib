/-
  Section 10 : The Salsa20 encryption function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.salsa20_expansion
import to_mathlib

open words
open ascii

namespace salsa20_encryption

-- a full key of 32 bytes
variable k : vector (bitvec byte_len) 32
-- the part 1 of a key
variable k₁ : vector (bitvec byte_len) 16
-- the part 2 of a key 
variable k₂ : vector (bitvec byte_len) 16
-- the maximum length of a a message to be encrypted/decrypted
variable l : fin (2^70)
-- a message as a list of bytes
variable m : list (bitvec byte_len)
-- the nonce as 16 bytes
variable nonce : vector (bitvec byte_len) 16

-- create keystream using expansion version 1
def get_keystream : vector (bitvec byte_len) 64 :=
  salsa20_expansion.salsa20_expansion_v1 k₁ k₂ nonce

-- given 2 lists of bitvec elements, this function will xor each element
-- of the list, using the first list length for the number of elements the
-- result will have.
def xor_2_lists : 
  list (bitvec byte_len) → list (bitvec byte_len) → list (bitvec byte_len)
| [] [] := []
| [] _ := []
| _ [] := []
| (x1 :: xs1) (x2 :: xs2) := list.insert (x1.xor x2) (xor_2_lists xs1 xs2)

-- encrypt a message only if it is less than 64 bytes where
-- keystream is always 64 bytes
def salsa20_encrypt : list (bitvec byte_len) :=
  if m.length > 63 then [] 
  else  
    xor_2_lists m (get_keystream k₁ k₂ nonce).to_list

-- TODO: theorem `dec_undoes_enc`

-- TODO: use expansion version 2

-- TODO: encrypt messages longer than 64 bytes

end salsa20_encryption
