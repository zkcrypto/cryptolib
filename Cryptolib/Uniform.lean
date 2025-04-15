/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Cryptolib.ToMathlib
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform distributions over ZMod q, BitVecs, and finite groups

This file defines the uniform distribution over a finite group as a PMF, including the
special case of Z_q, the integers modulo q.

It also provides two useful lemmas regarding uniform probabilities.
-/

variable (G : Type) [Fintype G] [Nonempty G] [Group G] [DecidableEq G]

noncomputable section

def uniform_bitvec (n : ℕ) : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

def uniform_grp : PMF G :=
  PMF.uniformOfFintype G

#check (uniform_grp G)

def uniform_zmod (n : ℕ) [NeZero n] : PMF (ZMod n) := uniform_grp (ZMod n)

def uniform_2 : PMF (ZMod 2) := uniform_zmod 2

lemma uniform_grp_prob :
    ∀ (g : G), (uniform_grp G) g = 1 / Fintype.card G := by
  intro g
  rw [uniform_grp, PMF.uniformOfFintype_apply, inv_eq_one_div]

lemma uniform_zmod_prob {n : ℕ} [NeZero n] :
    ∀ (a : ZMod n), (uniform_zmod n) a = 1/n := by
  intro a
  rw [uniform_zmod, uniform_grp, PMF.uniformOfFintype_apply]
  simp
