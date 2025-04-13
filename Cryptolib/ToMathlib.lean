import data.bitvec.basic
import data.zmod.basic
import group_theory.specific_groups.cyclic
import group_theory.subgroup.basic
import group_theory.subgroup.pointwise
import group_theory.order_of_element
import probability.probability_mass_function.basic
import probability.probability_mass_function.constructions
import probability.probability_mass_function.monad
import probability.probability_mass_function.uniform

/-
 ---------------------------------------------------------
  To multiset.range
 ---------------------------------------------------------
-/

lemma range_pos_ne_zero (n : ℕ) (n_pos : 0 < n): multiset.range n ≠ 0 :=
begin
  apply (multiset.card_pos).mp,
  rw multiset.card_range,
  exact n_pos,
end



/-
 ---------------------------------------------------------
  To group_theory.is_cyclic
 ---------------------------------------------------------
-/

def is_cyclic.generator {G : Type} [group G] [is_cyclic G] (g : G): Prop :=
   ∀ (x : G), x ∈ subgroup.zpowers g


/-
 ---------------------------------------------------------
  To bitvec.basic
 ---------------------------------------------------------
-/

namespace bitvec

instance fintype : Π (n : ℕ), fintype (bitvec n) := by {intro n, exact vector.fintype}

lemma card (n : ℕ) : fintype.card (bitvec n) = 2^n := card_vector n

lemma multiset_ne_zero (n : ℕ) : (bitvec.fintype n).elems.val ≠ 0 :=
begin
  apply (multiset.card_pos).mp,
  have h : multiset.card (fintype.elems (bitvec n)).val = 2^n := bitvec.card n,
  rw h,
  simp only [pow_pos, nat.succ_pos'],
end

-- missing bitvec lemmas used in streams ciphers.
-- TODO: they need proof
variable n : ℕ
variables a b c : bitvec n

lemma add_self : a + a = bitvec.zero n := by sorry
lemma add_assoc : a + b + c = a + (b + c) := by sorry
lemma zero_add : a = bitvec.zero n + a := by sorry
lemma add_self_assoc : b = a + (a + b) :=
  by rw [←add_assoc, add_self, ←zero_add]

lemma add_comm : a + b = b + a :=
begin
  -- idea: convert a and b to ℕ and prove comm there
  have ha := bitvec.to_nat a,
  have hb := bitvec.to_nat b,
  sorry,
end

lemma add_assoc_self : b = a + b + a :=
  by rw [add_comm, ←add_assoc, add_self, ←zero_add]

lemma add_assoc_self_reduce : c = a + (b + (a + (b + c))) :=
begin
  rw [←add_assoc, ←add_assoc, ←add_assoc],
  rw [←add_assoc_self, add_self, ←zero_add],
end

def to_list (length: ℕ) (B : bitvec length) : list bool :=
  vector.to_list B


end bitvec


/-
 ---------------------------------------------------------
  To data.basic.zmod, TO-DO Ask why this isn't already there
 ---------------------------------------------------------
-/

namespace zmod

-- instance group : Π (n : ℕ) [fact (0 < n)], group (zmod n) :=
--   by {intros n h, exact multiplicative.group}

instance group (n : ℕ) : group (zmod n) :=
  by {exact multiplicative.group}

end zmod



/-
 ---------------------------------------------------------
  To nat
 ---------------------------------------------------------
-/

lemma exists_mod_add_div (a b: ℕ) : ∃ (m : ℕ), a = a % b + b * m :=
begin
  use (a/b),
  exact (nat.mod_add_div a b).symm,
end



/-
 ---------------------------------------------------------
  To group
 ---------------------------------------------------------
-/

variables (G : Type) [fintype G] [group G]

namespace group

lemma multiset_ne_zero : (fintype.elems G).val ≠ 0 :=
begin
  have e : G := (_inst_2.one),
  have h1 : e ∈ (fintype.elems G).val :=  finset.mem_univ e,
  have h2 : 0 < multiset.card (fintype.elems G).val :=
  begin
    apply (multiset.card_pos_iff_exists_mem).mpr,
    exact Exists.intro e h1,
  end,
  exact multiset.card_pos.mp h2,
end

end group

/-
 ---------------------------------------------------------
  To list
 ---------------------------------------------------------
-/

namespace list

-- Given a list `l`, where each element is of type
-- `bitvec` of a given length `len`, convert this to a
-- `vector`, truncating the list at `len_vec` elements.
def to_vec_of_bitvec
  (len_bitvec : ℕ) (len_vec: ℕ) (l : list (bitvec len_bitvec)) :
  vector (bitvec len_bitvec ) len_vec :=
    ⟨list.take' len_vec l, list.take'_length len_vec l⟩

end list

/-
 ---------------------------------------------------------
  To ascii
 ---------------------------------------------------------
-/

namespace ascii

-- https://www.rapidtables.com/code/text/ascii-table.html

notation `ascii.A`          := 0b01000001 -- 65
notation `ascii.B`          := 0b01000010 -- 66
notation `ascii.C`          := 0b01000011 -- 67
notation `ascii.D`          := 0b01000100 -- 68
notation `ascii.E`          := 0b01000101 -- 69
notation `ascii.F`          := 0b01000110 -- 70
notation `ascii.G`          := 0b01000111 -- 71
notation `ascii.H`          := 0b01001000 -- 72
notation `ascii.I`          := 0b01001001 -- 73
notation `ascii.J`          := 0b01001010 -- 74
notation `ascii.K`          := 0b01001011 -- 75
notation `ascii.L`          := 0b01001100 -- 76
notation `ascii.M`          := 0b01001101 -- 77
notation `ascii.N`          := 0b01001110 -- 78
notation `ascii.O`          := 0b01001111 -- 79
notation `ascii.P`          := 0b01010000 -- 80
notation `ascii.Q`          := 0b01010001 -- 81
notation `ascii.R`          := 0b01010010 -- 82
notation `ascii.S`          := 0b01010011 -- 83
notation `ascii.T`          := 0b01010100 -- 84
notation `ascii.U`          := 0b01010101 -- 85
notation `ascii.V`          := 0b01010110 -- 86
notation `ascii.W`          := 0b01010111 -- 87
notation `ascii.X`          := 0b01011000 -- 88
notation `ascii.Y`          := 0b01011001 -- 89
notation `ascii.Z`          := 0b01011010 -- 90

notation `ascii.[space]`    := 0b00100000 -- 32
notation `ascii.[period]`   := 0b00101110 -- 46


end ascii
