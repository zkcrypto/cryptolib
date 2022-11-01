/-
  Section 2 : Words
  http://cr.yp.to/snuffle/spec.pdf

  This file formalize the ARX building blocks of salsa20:
  https://en.wikipedia.org/wiki/Block_cipher#ARX_(add%E2%80%93rotate%E2%80%93XOR)

  Utility functions to be used in higher levels of salsa20 are also here.

  Numeric examples are taken form the spec.
-/
import data.bitvec.basic
import data.list.basic
import data.zmod.basic
import tactics

import to_mathlib

namespace words

-- A byte is a bitvec of 8 bits
def byte_len : ℕ := 8
-- A word is a bitvec of 32 bits
def word_len : ℕ := 32 

-- sum of 2 words

-- sums are done modulo 2^32
def mod : ℕ := (2^word_len)

-- convert a 32 bitvector to a zmod
def bitvec_as_mod (v : bitvec word_len) : zmod mod := v.to_nat

-- convert two bitvec to the sum of them modulo 2^32
def add_bitvecs_as_mod (u v : bitvec word_len) : zmod mod := bitvec_as_mod u + bitvec_as_mod v

-- convert two bitvec to the rest of them modulo 2^32
def substract_bitvecs_as_mod (u v : bitvec word_len) : zmod mod := bitvec_as_mod u - bitvec_as_mod v

-- convert a mod 2^32 to a nat
def mod_as_nat (sum : zmod mod) : ℕ := sum.val

-- convert a nat to a bitvec
def nat_as_bitvec (n : ℕ) : bitvec word_len := bitvec.of_nat word_len n

-- the inverse of the zmod sum of 2 bitvectors is the substraction of them
def zmod_addition_inverse (a : zmod mod) : ℕ := mod - a.val  

-- xor

-- axioms

-- a ⊕ a = 0
axiom xor_equals_eq_zero (a : bitvec word_len) : a.xor a = bitvec.zero word_len
-- a ⊕ 0 = a
axiom xor_zero (a : bitvec word_len) : a.xor (bitvec.zero word_len) = a
-- (a ⊕ b) ⊕ b = a
axiom xor_assoc_v1 (a b : bitvec word_len) : (a.xor b).xor b = a
-- (a ⊕ b) ⊕ a = b
axiom xor_assoc_v2 (a b : bitvec word_len) : (a.xor b).xor a = b

-- theorems

-- applying the same xor_by twice reverses to the original value 
lemma xor_twice_reverses (orig xor_by : bitvec word_len) : orig = (orig.xor xor_by).xor xor_by :=
begin
  rw xor_assoc_v1,
end

-- c = a ⊕ b ↔ (a = c ⊕ b) ∧ (b = c ⊕ a)
theorem xor_is_its_own_inverse (a b c : bitvec word_len) : c = a.xor b ↔ (a = c.xor b) ∧ (b = c.xor a) :=
begin
  split,
  {
    intro h,
    split,
    {
      rw h,
      rw xor_assoc_v1,
    },
    {
      rw h,
      rw xor_assoc_v2,
    },
  },
  {
    norm_num,
    intros h1 h2,
    rw h1,
    rw xor_assoc_v1
  }
end

-- rotation

-- Implements DJB's definition of '<<<' : https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6
def rotl (input: bitvec 32) (shift : fin 32) : bitvec 32 :=
  (input.shl shift).or (input.ushr (32 - shift))

-- Inverse of rotl
def rotl_inv (input: bitvec 32) (shift : fin 32) : bitvec 32 :=
  (input.ushr shift).or (input.shl (32 - shift))

-- theorems

-- the inverse always undoes rotl 
theorem rotl_inv_undoes_rotl (input: bitvec 32) (shift : fin 32) : 
  input = rotl_inv (rotl input shift) shift := 
begin
  unfold rotl,
  unfold rotl_inv,
  sorry,
end


end words
