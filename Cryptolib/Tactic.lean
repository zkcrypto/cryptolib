/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Mathlib.Probability.Distributions.Uniform
/-!
# Cryptolib tactics
This file provides the `bindskip` and `bindconst` tactics to help prove equivalences
between PMFs.
-/

variable {α β : Type}

lemma bind_skip' (p : PMF α) (f g : α → PMF β) :
    (∀ (a : α), f a = g a) → p.bind f = p.bind g := by
  intro ha
  ext
  simp
  simp_rw [ha]

lemma bind_skip_const' (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ (a : α), f a = pb) → pa.bind f = pb := by
  intro ha
  ext
  simp
  simp_rw [ha]
  simp [ENNReal.tsum_mul_right]

-- setup_tactic_parser
-- meta def tactic.interactive.bind_skip  (x : parse (tk "with" *> ident)?) : tactic unit :=
-- do `[apply bind_skip'],
--   let a := x.get_or_else `_,
--   tactic.interactive.intro a
syntax "bind_skip" : tactic
macro_rules
  | `(tactic|bind_skip) => `(tactic|apply bind_skip')
syntax "bind_skip" "with" ident : tactic
macro_rules
  | `(tactic|bind_skip with x) => `(tactic|apply bind_skip')

-- meta def tactic.interactive.bind_skip_const  (x : parse (tk "with" *> ident)?) : tactic unit :=
-- do `[apply bind_skip_const'],
--   let a := x.get_or_else `_,
--   tactic.interactive.intro a
syntax "bind_skip_const" "with" ident : tactic
macro_rules
  | `(tactic|bind_skip_const with x) => `(tactic|apply bind_skip_const')
