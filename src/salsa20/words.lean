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
def sum_as_mod (u v : bitvec word_len) : zmod mod := 
  bitvec_as_mod u + bitvec_as_mod v

-- convert a mod 2^32 to a nat
def mod_as_nat (sum : zmod mod) : ℕ := sum.val

-- convert a nat to a bitvec
def nat_as_bitvec (n : ℕ) : bitvec word_len := bitvec.of_nat word_len n

-- xor = just bitwise xor
def xor' (v1 v2 : bitvec word_len): bitvec word_len :=
  v1.xor v2

-- rotation
-- Implements DJB's definition of '<<<' : https://github.com/alexwebr/salsa20/blob/master/salsa20.c#L6
def rotl (input: bitvec 32) (shift : fin 32) : bitvec 32 :=
  (input.shl shift).or (input.ushr (32 - shift))


end words
