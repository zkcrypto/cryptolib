/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo, Alfredo Garcia
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Simple
-- import Mathlib.GroupTheory.Subgroup.Pointwise
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# General lemmas for inclusion into mathlib

These are lemmas necessary for using Mathlib with cryptography, that should be upstreamed
into Mathlib itself.
-/

/-
 ---------------------------------------------------------
  To multiset.range
 ---------------------------------------------------------
-/

lemma range_pos_ne_zero (n : ℕ) (n_pos : 0 < n) : Multiset.range n ≠ 0 := by
  apply (Multiset.card_pos).mp
  rw [Multiset.card_range]
  exact n_pos



/-
 ---------------------------------------------------------
  To group_theory.is_cyclic
 ---------------------------------------------------------
-/

def is_cyclic.generator {G : Type} [Group G] [IsCyclic G] (g : G): Prop :=
   ∀ (x : G), x ∈ Subgroup.zpowers g


/-
 ---------------------------------------------------------
  To bitvec.basic
 ---------------------------------------------------------
-/

namespace BitVec

instance fintype : ∀ (n : ℕ), Fintype (BitVec n) := by
  intro n
  sorry
  -- exact Vector.fintype

lemma card (n : ℕ) : Fintype.card (BitVec n) = 2^n := by sorry
  -- card_vector n

lemma multiset_ne_zero (n : ℕ) : (BitVec.fintype n).elems.val ≠ 0 := by
  apply (Multiset.card_pos).mp
  -- have h : Multiset.card (Fintype.elems (BitVec n)).val = 2^n := BitVec.card n
  -- rw [h]
  -- simp only [pow_pos, nat.succ_pos']
  sorry

-- missing bitvec lemmas used in streams ciphers.
-- TODO: they need proof
variable (n : ℕ)
variable (a b c : BitVec n)

lemma add_self : a + a = BitVec.zero n := by sorry
-- lemma add_assoc : a + b + c = a + (b + c) := by sorry
-- lemma zero_add : a = BitVec.zero n + a := by sorry
lemma add_self_assoc : b = a + (a + b) := by sorry
  -- rw [←add_assoc, add_self, ←zero_add]

-- lemma add_comm : a + b = b + a := by
--   -- idea: convert a and b to ℕ and prove comm there
--   have ha := bitvec.to_nat a
--   have hb := bitvec.to_nat b
--   sorry

lemma add_assoc_self : b = a + b + a := by
  -- rw [add_comm, ←add_assoc, add_self, ←zero_add]
  sorry

lemma add_assoc_self_reduce : c = a + (b + (a + (b + c))) := by
  rw [←add_assoc, ←add_assoc, ←add_assoc]
  -- rw [←add_assoc_self, add_self, ←zero_add]
  sorry

-- def to_list (length: ℕ) (B : BitVec length) : List Bool :=
--   Vector.to_list B


end BitVec


/-
 ---------------------------------------------------------
  To data.basic.zmod, TO-DO Ask why this isn't already there
 ---------------------------------------------------------
-/

namespace ZMod

instance group (n : ℕ) : Group (ZMod n) :=
  inferInstanceAs (Group (Multiplicative (ZMod n)))

end ZMod



/-
 ---------------------------------------------------------
  To nat
 ---------------------------------------------------------
-/

lemma exists_mod_add_div (a b: ℕ) : ∃ (m : ℕ), a = a % b + b * m := by
  use (a/b)
  exact (Nat.mod_add_div a b).symm



/-
 ---------------------------------------------------------
  To group
 ---------------------------------------------------------
-/

variable (G : Type) [Fintype G] [Group G]

namespace Group

-- lemma multiset_ne_zero : (Fintype.elems G).val ≠ 0 := by
--   sorry
  -- have e : G := (_inst_2.one)
  -- have h1 : e ∈ (Fintype.elems G).val :=  Finset.mem_univ e
  -- have h2 : 0 < multiset.card (fintype.elems G).val := by
  --   apply (multiset.card_pos_iff_exists_mem).mpr
  --   exact Exists.intro e h1
  -- exact multiset.card_pos.mp h2

end Group

/-
 ---------------------------------------------------------
  To list
 ---------------------------------------------------------
-/

namespace List

-- Given a list `l`, where each element is of type
-- `BitVec` of a given length `len`, convert this to a
-- `Vector`, truncating the list at `len_vec` elements.
def to_vec_of_bitvec
  (len_bitvec : ℕ) (len_vec: ℕ) (l : List (BitVec len_bitvec)) :
  Vector (BitVec len_bitvec ) len_vec :=
    ⟨List.take len_vec l, sorry⟩ --List.take_length len_vec l⟩

end List

/-
 ---------------------------------------------------------
  To ascii
 ---------------------------------------------------------
-/

namespace ascii

-- https://www.rapidtables.com/code/text/ascii-table.html

notation "ascii.A"          => 0b01000001 -- 65
notation "ascii.B"          => 0b01000010 -- 66
notation "ascii.C"          => 0b01000011 -- 67
notation "ascii.D"          => 0b01000100 -- 68
notation "ascii.E"          => 0b01000101 -- 69
notation "ascii.F"          => 0b01000110 -- 70
notation "ascii.G"          => 0b01000111 -- 71
notation "ascii.H"          => 0b01001000 -- 72
notation "ascii.I"          => 0b01001001 -- 73
notation "ascii.J"          => 0b01001010 -- 74
notation "ascii.K"          => 0b01001011 -- 75
notation "ascii.L"          => 0b01001100 -- 76
notation "ascii.M"          => 0b01001101 -- 77
notation "ascii.N"          => 0b01001110 -- 78
notation "ascii.O"          => 0b01001111 -- 79
notation "ascii.P"          => 0b01010000 -- 80
notation "ascii.Q"          => 0b01010001 -- 81
notation "ascii.R"          => 0b01010010 -- 82
notation "ascii.S"          => 0b01010011 -- 83
notation "ascii.T"          => 0b01010100 -- 84
notation "ascii.U"          => 0b01010101 -- 85
notation "ascii.V"          => 0b01010110 -- 86
notation "ascii.W"          => 0b01010111 -- 87
notation "ascii.X"          => 0b01011000 -- 88
notation "ascii.Y"          => 0b01011001 -- 89
notation "ascii.Z"          => 0b01011010 -- 90

notation "ascii.[space]"    => 0b00100000 -- 32
notation "ascii.[period]"   => 0b00101110 -- 46


end ascii
