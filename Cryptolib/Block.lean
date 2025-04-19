/-
 -----------------------------------------------------------
  Formalization and correctness of block ciphers
 -----------------------------------------------------------
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped Matrix

namespace Hill

/-!
# Hill cipher: A generalization of the affine cipher

If block = 2 then this is a digraphic cipher.
If block > 2 then this is a poligraphic cipher.
If block = 1 then this is a reduction to the affine cipher.
-/

-- All operations will be mod 26 (English language character set).
def m : ℕ := 26

-- The size of the block
variable (block : ℕ)

-- The key matrix
variable (A : Matrix (Fin block) (Fin block) (ZMod m))

-- The plaintext vector
variable (P : Matrix (Fin block) (Fin 1) (ZMod m))

-- The ciphertext vector
variable (C : Matrix (Fin block) (Fin 1) (ZMod m))

-- Encryption
def encrypt : (Matrix (Fin block) (Fin 1) (ZMod m)) := A * P

-- Decryption
noncomputable def decrypt : (Matrix (Fin block) (Fin 1) (ZMod m)) := A⁻¹ * P

-- Proof of correctness
lemma dec_undoes_enc (h : A.det = 1): P = decrypt block A (encrypt block A P) := by
  unfold encrypt
  unfold decrypt
  simp_all only [isUnit_one, Matrix.nonsing_inv_mul_cancel_left]

end Hill
