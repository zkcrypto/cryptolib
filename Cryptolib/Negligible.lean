/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Monotonicity

/-!
# Negligible functions.

This file defines negligible functions and provides several useful lemmas regarding
negligible functions.

  TO-DO connect with security parameter, (or not, as in Nowak),
  and refactor proofs/improve variable naming
-/

/-
  A function f : ℤ≥1 → ℝ is called negligible if
  for all c ∈ ℝ>0 there exists n₀ ∈ ℤ≥1 such that
  n₀ ≤ n →  |f(n)| < 1/n^c
-/
def negligible (f : ℕ → ℝ) :=
  ∀ c > 0, ∃ n₀, ∀ n,
  n₀ ≤ n → abs (f n) < 1 / (n : ℝ)^c

def negligible' (f : ℕ → ℝ) :=
  ∀ (c : ℝ), ∃ (n₀ : ℕ), ∀ (n : ℕ),
  0 < c → n₀ ≤ n → abs (f n) < 1 / n^c

lemma negl_equiv (f : ℕ → ℝ) : negligible f ↔ negligible' f := by
  constructor
  {-- Forward direction
    intros h c
    have arch := exists_nat_gt c
    cases' arch with k hk
    let k₀ := max k 1
    have k_leq_k₀ : k ≤ k₀ := le_max_left k 1
    have kr_leq_k₀r : (k:ℝ) ≤ k₀ := Nat.cast_le.mpr k_leq_k₀
    have k₀_pos : 0 < k₀ := by {apply le_max_right k 1}
    have a := h k₀ k₀_pos

    -- use k₀
    -- intros n c_pos hn
    -- have hnnn : k ≤ n := by linarith

    cases' a with n' hn₀
    let n₀ := max n' 1
    have n₀_pos : 0 < n₀ := by apply le_max_right n' 1
    have n'_leq_n₀ : n' ≤ n₀ := le_max_left n' 1
    use n₀
    intros n c_pos hn
    have hnnn : n' ≤ n := by linarith

    have b : (n : ℝ)^c ≤ (n : ℝ)^(k₀ : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      norm_cast
      linarith
      linarith
    have daf : (n : ℝ)^(k₀ : ℝ) = (n : ℝ)^k₀ := (n : ℝ).rpow_natCast k₀
    rw [daf] at b
    have d : 1 / (n : ℝ)^k₀ ≤ 1 / n^c := by
      apply one_div_le_one_div_of_le
      { -- Proving 0 < (n:ℝ) ^ c
        apply Real.rpow_pos_of_pos
        norm_cast
        linarith
      }
      {exact b}
    have goal : abs (f n) < 1 / n^c :=
    calc
      abs (f n) < 1 / (n : ℝ)^k₀ := hn₀ n hnnn
      _         ≤ 1 / n^c := d
    exact goal
  }

  {-- Reverse direction
    intros h c hc
    cases' h c with n₀ hn₀
    use n₀
    intros n hn
    have goal := hn₀ n (Nat.cast_pos.mpr hc) hn
    rw [(n : ℝ).rpow_natCast c] at goal
    exact goal
  }

lemma zero_negl : negligible (λ_ => 0) := by
  intros c hc
  use 1
  intros n hn
  norm_num
  apply pow_pos
  have h : 0 < n := by linarith
  exact Nat.cast_pos.mpr h

lemma negl_add_negl_negl {f g : ℕ → ℝ} : negligible f → negligible g → negligible (f + g) := by
  intros hf hg
  intros c hc
  have hc1 : (c+1) > 0 := Nat.lt.step hc
  have hf2 := hf (c+1) hc1
  have hg2 := hg (c+1) hc1
  cases' hf2 with nf hnf
  cases' hg2 with ng hng
  let n₀ := max (max nf ng) 2
  use n₀
  intros n hn
  let nr := (n:ℝ)
  have n_eq_nr : (n:ℝ) = nr := by rfl

  have tn : max nf ng ≤ n₀ := le_max_left (max nf ng) 2
  have t2n₀ : 2 ≤ n₀ := le_max_right (max nf ng) 2
  have t2n : 2 ≤ n := by linarith
  have t2nr : 2 ≤ nr := by
    have j := Nat.cast_le.mpr t2n
    rw [n_eq_nr] at j
    norm_num at j
    exact j
    exact is_R_or_C.char_zero_R_or_C
  have tnr_pos : 0 < nr := by linarith

  have t2na : (1 / nr) * (1/nr^c) ≤ (1 / (2 : ℝ)) * (1 / nr^c) := by
    have ht2 : 0 < (1 / nr^c) := by {apply one_div_pos.mpr; exact pow_pos tnr_pos c}
    apply (mul_le_mul_right ht2).mpr
    apply one_div_le_one_div_of_le
    exact zero_lt_two
    exact t2nr

  have tnr2 : 1 / nr^(c + 1) ≤ (1 / (2 : ℝ)) * (1 / nr^c) :=
  calc
    1 / nr ^ (c + 1) = (1 / nr)^(c + 1) := by rw [one_div_pow]
    _                = (1 / nr)^c * (1 / nr) := pow_succ (1 / nr) c
    _                = (1 / nr) * (1 / nr)^c := by linarith
    _                = (1 / nr) * (1 / nr^c) := by rw [one_div_pow]
    _                ≤ (1 / (2 : ℝ)) * (1 / nr^c) := t2na

  have tnf : nf ≤ n :=
  calc
    nf  ≤ n₀ := le_of_max_le_left tn
    _   ≤ n  := hn
  have tfn := hnf n tnf
  have tf : abs (f n) < (1 / (2 : ℝ)) * (1 / nr^c) := by linarith

  have tng : ng ≤ n :=
  calc ng  ≤ n₀ := le_of_max_le_right tn
       _   ≤ n  := hn
  have tgn := hng n tng
  have tg : abs (g n) < (1/(2:ℝ)) * (1/nr^c) := by linarith

  have goal : abs ((f + g) n) < 1 / nr ^ c :=
  calc
    abs ((f + g) n) = abs (f n + g n) := by rw [Pi.add_apply f g n]
    _               ≤ abs (f n) + abs (g n) := abs_add (f n) (g n)
    _               < (1/(2:ℝ)) * (1/nr^c) + abs (g n) := by linarith
    _               < (1/(2:ℝ)) * (1/nr^c) + (1/(2:ℝ)) * (1/nr^c) := by linarith
    _               = 1/nr^c := by ring_nf
  exact goal

lemma bounded_negl_negl {f g : ℕ → ℝ} (hg : negligible g):
    (∀ n, abs (f n) ≤ abs (g n)) → negligible f := by
  intro h
  intros c hc
  have hh := hg c hc
  cases' hh with n₀ hn₀
  use n₀
  intros n hn
  have goal : abs (f n) < 1 / (n : ℝ) ^ c :=
  calc
    abs (f n) ≤ abs (g n) := h n
    _         < 1 / (n : ℝ)^c := hn₀ n hn
  exact goal

lemma nat_mul_negl_negl {f : ℕ → ℝ} (m : ℕ):
    negligible f → negligible (λn => m * (f n)) := by
  intros hf
  induction' m with k hk
  { -- Base case
    norm_num
    exact zero_negl
  }
  { -- Inductive step
    norm_num
    have d : (λn => ((k : ℝ) + 1) * (f n)) = (λn => (k : ℝ) * (f n)) + (λn => f n) :=
      by sorry --repeat' {ring_nf}
    rw [d]
    apply negl_add_negl_negl
    exact hk
    exact hf
  }

lemma const_mul_negl_negl {f : ℕ → ℝ} (m : ℝ) :
    negligible f → negligible (λn => m * (f n)) := by
  intro hf
  -- Use Archimedian property to get arch : ℕ with abs m < arch
  have arch := exists_nat_gt (abs m)
  cases' arch with k hk
  apply bounded_negl_negl

  { -- Demonstrate a negligible function kf
    have kf_negl := nat_mul_negl_negl k hf
    exact kf_negl
  }

  { -- Show kf bounds mf from above
    intro n
    have h : abs m ≤ abs (k : ℝ) :=
    calc
      abs m ≤ (k : ℝ) := le_of_lt hk
      _     = abs (k : ℝ) := (Nat.abs_cast k).symm

    have goal : abs (m * f n) ≤ abs ((k : ℝ) * f n) :=
    calc
      abs (m * f n) = abs   m      * abs (f n) := by rw [abs_mul]
      _             ≤ abs  (k : ℝ) * abs (f n) := mul_le_mul_of_nonneg_right h (abs_nonneg (f n))
      _             = abs ((k : ℝ) *      f n) := by rw [<- abs_mul]

    exact goal
  }

theorem neg_exp_negl : negligible ((λn => (1 : ℝ) / 2^n) : ℕ → ℝ) := by sorry

-- Need to prove lim n^c/2^n = 0 by induction on c using L'Hopital's rule to apply inductive
-- hypothesis
/-
  let m := 2
  have hm : 0 < 2 := zero_lt_two
  have c2_negl := c2_mul_neg_exp_is_negl 2 hm
  have r : (λ (n : ℕ) => 16 * (1 / (2 ^ n * 16)): ℕ → ℝ) = ((λn => (1:ℝ)/2^n): ℕ → ℝ) := by
    funext
    have h : (1:ℝ) / 2^n / 16 = (1:ℝ) / (2^n * 16) := div_div_eq_div_mul 1 (2^n) 16
    rw [<- h]
    ring_nf

  have goal := const_mul_negl_is_negl 16 c2_negl
  norm_num at goal
  rw [<-r]
  exact goal
-/
