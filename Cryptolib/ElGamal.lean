/-
Copyright (c) 2021 Joey Lupo
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Joey Lupo
-/
import Cryptolib.DecisionalDiffieHellman
import Cryptolib.PublicKeyEncryption
import Cryptolib.Tactic
import Cryptolib.ToMathlib
import Cryptolib.Uniform
import Mathlib.Tactic.Cases

/-!
# Correctness and semantic security of ElGamal public-key encryption scheme

This file contains the formal specification of the ElGamal public key encryption protocol,
and the formal proofs of correctness.
-/

section ElGamal

noncomputable section

variable (G : Type) [Fintype G] [CommGroup G] [DecidableEq G]
         (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
         (q : ℕ) [NeZero q] [Group (ZMod q)] (G_card_q : Fintype.card G = q)
         (A_state : Type)

include g_gen_G G_card_q

variable (A1 : G → PMF (G × G × A_state))
         (A2 : G → G → A_state → PMF (ZMod 2))

def A2' : G × G → A_state → PMF (ZMod 2) := λ (gg : G × G) => A2 gg.1 gg.2

-- generates a public key `g^x.val`, and private key `x`
def keygen : PMF (G × (ZMod q)) :=
do
  let x ← uniform_zmod q
  pure (g^x.val, x)

#check keygen
-- encrypt takes a pair (public key, message)
def encrypt (pk m : G) : PMF (G × G) :=
do
  let y ← uniform_zmod q
  pure (g^y.val, pk^y.val * m)

-- `x` is the secret key, `c.1` is g^y, the first part of the
-- cipher text returned from encrypt, and `c.2` is the
-- second value returned from encrypt
def decrypt (x : ZMod q)(c : G × G) : G :=
  (c.2 / (c.1^x.val))

/-
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

lemma decrypt_eq_m (m : G) (x y: ZMod q) :
    decrypt G /- g g_gen_G -/ q /- G_card_q -/ x ((g^y.val), ((g^x.val)^y.val * m)) = m := by
  simp [decrypt]
  rw [(pow_mul g x.val y.val).symm]
  rw [(pow_mul g y.val x.val).symm]
  rw [mul_comm y.val x.val]
  rw [div_eq_mul_inv]
  rw [mul_assoc, mul_comm m _, <- mul_assoc, mul_inv_cancel _]
  exact one_mul m

-- set_option trace.ext true
-- set_option trace.simplify true


theorem elgamal_correctness : PkeCorrectness (keygen G g /- g_gen_G -/ q /- G_card_q -/) (encrypt G g /- g_gen_G -/ q /- G_card_q -/) (decrypt G /- g g_gen_G -/ q /- G_card_q -/) := by
  -- simp_intros [PkeCorrectness]
  simp [PkeCorrectness]
  -- intro m
  -- simp [enc_dec, keygen, encrypt, bind]
  -- bind_skip_const with x
  -- simp [pure]
  -- bind_skip_const with y
  simp [enc_dec, keygen, encrypt, bind, pure]
  simp_rw [decrypt_eq_m]
  simp only [eq_self_iff_true, if_true]



/-
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

def D (gx gy gz : G) : PMF (ZMod 2) :=
do
  let m ← A1 gx -- give G, g, q, h_1 (gx) to A1 and run to get two messages
  let b ← uniform_2 -- choose b uniformly
  let mb ← pure (if b = 0 then m.1 else m.2.1)
  let b' ← A2 gy (gz * mb) m.2.2 -- Katz & Lindell theorem 12.18 (elgamal)
  pure (1 + b + b') -- output the same bit - means it was able to break the encryption

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning the semantic security game (i.e. guessing the correct bit),
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0.
-/


theorem SSG_DDH0 : SSG (keygen G g /- g_gen_G -/ q /- G_card_q -/) (encrypt G g /- g_gen_G -/ q /- G_card_q -/) A1 (A2' G /- g g_gen_G q G_card_q -/ A_state A2) = DDH0 G g /- g_gen_G -/ q /- G_card_q -/ (D G /- g g_gen_G q G_card_q -/ A_state A1 A2) := by
  simp only [SSG, DDH0, bind, keygen, encrypt, D]
  simp_rw [PMF.bind_bind (uniform_zmod q)]
  bind_skip with x
  simp [pure]
  simp_rw [PMF.bind_comm (uniform_zmod q)]
  bind_skip with m
  bind_skip with b
  bind_skip with y
  simp only [A2']
  rw [pow_mul g x.val y.val]


def Game1 : PMF (ZMod 2) :=
do
  let x ← uniform_zmod q
  let y ← uniform_zmod q
  let m ← A1 (g^x.val)
  let b ← uniform_2
  let ζ ← (do let z ← uniform_zmod q; let mb ← pure (if b = 0 then m.1 else m.2.1); pure (g^z.val * mb))
  let b' ← A2 (g^y.val) ζ m.2.2
  pure (1 + b + b')

def Game2 : PMF (ZMod 2) :=
do
  let x ← uniform_zmod q
  let y ← uniform_zmod q
  let m ← A1 (g^x.val)
  let b ← uniform_2
  let ζ ← (do let z ← uniform_zmod q; pure (g^z.val))
  let b' ← A2 (g^y.val) ζ m.2.2
  pure (1 + b + b')

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of D winning the game DDH1.
-/

theorem Game1_DDH1 : (Game1 G g /- g_gen_G -/ q /- G_card_q -/ A_state A1 A2) = DDH1 G g /- g_gen_G -/ q /- G_card_q -/ (D G /- g g_gen_G q G_card_q -/ A_state A1 A2) := by
  simp only [DDH1, Game1, bind, D]
  bind_skip with x
  bind_skip with y
  simp_rw [PMF.bind_bind (A1 _)]
  -- conv_rhs {rw [PMF.bind_comm (uniform_zmod q)]}
  bind_skip with m
  simp_rw [PMF.bind_bind (uniform_zmod q)]
  -- conv_lhs {rw [PMF.bind_comm (uniform_2)]}
  bind_skip with z
  -- conv_rhs {rw [PMF.bind_bind (uniform_2)]}
  bind_skip with b
  simp_rw [PMF.bind_bind]
  bind_skip with mb
  simp [pure]

lemma exp_bij :
    Function.Bijective (λ (z : ZMod q) => g ^ z.val) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor

  { -- (λ (z : ZMod q) => g ^ z.val) surjective
    intro gz
    have hz := Subgroup.mem_zpowers_iff.mp (g_gen_G gz)
    cases' hz with z hz
    cases' z

    { -- Case : z = z' for (z : ℕ)
      let zq := z % q
      use zq
      have h1 : (λ (z : ZMod q) => g ^ z.val) ↑zq = g ^ (zq : ZMod q).val := rfl
      rw [h1]
      rw [ZMod.val_cast_of_lt]
      {
        have goal : gz = g ^ zq :=
        calc
          gz = g ^ Int.of_nat z := hz.symm
          _  = g ^ z := by simp
          _  = g ^ (z % q + q * (z / q)) := by rw [Nat.mod_add_div z q]
          _  = g ^ (z % q) * g ^ (q * (z / q)) := by rw [pow_add]
          _  = g ^ (z % q) * (g ^ q) ^ (z / q) := by rw [pow_mul]
          _  = g ^ (z % q) * (g ^ Fintype.card G) ^ (z / q) := by rw [<- G_card_q]
          _  = g ^ (z % q) := by simp [pow_card_eq_one]
          _  = g ^ zq := rfl
        exact goal.symm
      }
      exact Nat.mod_lt z (Nat.pos_of_ne_zero _inst_4.out)
    }

    { -- Case : z = - (1 + z') for (z' : ℕ)
      let zq := (q - (z + 1) % q ) % q
      use zq
      have h1 : (λ (z : ZMod q) => g ^ z.val) ↑zq = g ^ (zq : ZMod q).val := rfl
      rw [h1]
      rw [ZMod.val_cast_of_lt]
      {
        have h1 : (z + 1) % q ≤ Fintype.card G := by
          rw [G_card_q]
          apply le_of_lt
          exact Nat.mod_lt _ (Nat.pos_of_ne_zero _inst_4.out)

        have goal : gz = g ^ zq :=
        calc
          gz = g ^ Int.neg_succ_of_nat z := hz.symm
          _  = (g ^ z.succ)⁻¹  := by rw [zpow_neg_succ_of_nat]
          _  = (g ^ (z + 1))⁻¹ := rfl
          _  = (g ^ ((z + 1) % Fintype.card G))⁻¹ := by rw [pow_eq_mod_card (z + 1)]
          _  = (g ^ ((z + 1) % q))⁻¹ := by rw [G_card_q]
          _  = g ^ (Fintype.card G - (z + 1) % q) := inv_pow_eq_card_sub_pow G g _ h1
          _  = g ^ (q - ((z + 1) % q)) := by rw [G_card_q]
          _  = g ^ ((q - (z + 1) % q) % q
                  + q * ((q - (z + 1) % q) / q)) := by rw [Nat.mod_add_div]
          _  = g ^ ((q - (z + 1) % q) % q)
                  * g ^ (q * ((q - (z + 1) % q) / q)) := by rw [pow_add]
          _  = g ^ ((q - (z + 1) % q) % q)
                  * (g ^ q) ^ ((q - (z + 1) % q) / q) := by rw [pow_mul]
          _  = g ^ ((q - (z + 1) % q) % q)
                  * (g ^ Fintype.card G) ^ ((q - (z + 1) % q) / q) := by rw [<- G_card_q]
          _  = g ^ ((q - (z + 1) % q) % q) := by simp [pow_card_eq_one]
          _  = g ^ zq := rfl
        exact goal.symm
      }

      exact Nat.mod_lt _ (Nat.pos_of_ne_zero _inst_4.out)
    }
  }

  { -- Fintype.card (ZMod q) = Fintype.card G
    rw [G_card_q]
    exact ZMod.card q
  }

lemma exp_mb_bij (mb : G) : Function.Bijective (λ (z : ZMod q) => g ^ z.val * mb) := by
  have h :
      (λ (z : ZMod q) => g ^ z.val * mb) =
      ((λ (m : G) => (m * mb)) ∘ (λ (z : ZMod q) => g ^ z.val)) := by
    simp
  rw [h]
  apply Function.Bijective.comp

  { -- (λ (m : G), (m * mb)) bijective
    refine Finite.injective_iff_bijective.mp _
    intros x a hxa
    simp at hxa
    exact hxa
  }

  { -- (λ (z : ZMod q), g ^ z.val) bijective
    exact exp_bij G g g_gen_G q G_card_q
  }

lemma G1_G2_lemma1 (x : G) (exp : ZMod q → G) (exp_bij : Function.Bijective exp) :
    ∑' (z : ZMod q), ite (x = exp z) (1 : NNReal) 0 = 1 := by
  have inv :=  Function.bijective_iff_has_inverse.mp exp_bij
  cases' inv with exp_inv
  have bij_eq : ∀ (z : ZMod q), (x = exp z) = (z = exp_inv x) := by
    intro z
    simp
    constructor

    { -- (x = exp z) → (z = exp_inv x)
      intro h
      have h1 : exp_inv x = exp_inv (exp z) := congr_arg exp_inv h
      rw [inv_h.left z] at h1
      exact h1.symm
    }

    { -- (z = exp_inv x) → (x = exp z)
      intro h
      have h2 : exp z = exp (exp_inv x) := congr_arg exp h
      rw [inv_h.right x] at h2
      exact h2.symm
    }
  simp_rw [bij_eq]
  simp

lemma G1_G2_lemma2 (mb : G) :
    (uniform_zmod q).bind (λ (z : ZMod q) => pure (g^z.val * mb)) =
    (uniform_zmod q).bind (λ (z : ZMod q) => pure (g^z.val)) := by
  simp [PMF.bind]
  simp_rw [uniform_zmod_prob]
  apply funext
  intro
  -- ext
  simp only [pure]
  simp only [PMF.pure]
  simp only [coe_fn]
  simp only [has_coe_to_fun.coe]
  simp only [fun_like.coe]
  simp only [ennreal.tsum_mul_left]
  -- simp only [pure, PMF.pure, coe_fn, has_coe_to_fun.coe, nnreal.tsum_mul_left]
  norm_cast
  simp
  rw [@mul_eq_mul_left_iff ennreal ↑q _ _]
  simp only [one_div, mul_eq_mul_left_iff, inv_eq_zero, nat.cast_eq_zero]
  simp only [one_div]
  congr 2
  intros
  -- simp_rw [mul_eq_mul_left_iff] at * -- Seems that this is not going to the same depth as the same tactic in 3.3? There is an extra simplification step in the 3.3 version that seems to reach the intended target
  simp
  simp only [inv_eq_zero]
  simp only [nat.cast_eq_zero] -- added trace.simplify true - must be something in here...
  apply or.intro_left -- tried apply iff.intro here, but that seems like maybe a deadend...
  repeat {rw [G1_G2_lemma1 x]}
  rw [G1_G2_lemma1 _ _ (exp_mb_bij mb)]
  intros
  exact exp_mb_bij mb

#check exp_bij
#check G1_G2_lemma1 _ _ (exp_mb_bij _)
#check G1_G2_lemma1
#check exp_mb_bij

lemma G1_G2_lemma3 (m : PMF G) :
    m.bind (λ (mb : G) => (uniform_zmod q).bind (λ (z : ZMod q) => pure (g^z.val * mb))) =
    (uniform_zmod q).bind (λ (z : ZMod q) => pure (g^z.val)) := by
  simp_rw [G1_G2_lemma2 _]
  bind_skip_const with m
  congr

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of the attacker winning Game2.
-/
theorem Game1_Game2 : Game1 = Game2 := by
  simp only [Game1, Game2]
  bind_skip with x
  bind_skip with y
  bind_skip with m
  bind_skip with b
  simp [bind, -PMF.bind_pure, -PMF.bind_bind]
  simp_rw [PMF.bind_comm (uniform_zmod q)]
  rw [G1_G2_lemma3]

lemma G2_uniform_lemma (b' : ZMod 2) :
    uniform_2.bind (λ (b : ZMod 2) => pure (1 + b + b')) = uniform_2 := by
  fin_cases b'

  . -- b = 0
    ring_nf
    ext
    simp [uniform_2]
    rw [uniform_zmod_prob] -- a
    simp_rw [uniform_zmod_prob]
    simp [NNReal.tsum_mul_left]
    have zmod_eq_comm : ∀ (x : ZMod 2), (a = 1 + x) = (x = 1 + a) := by
      intro x
      fin_cases a

      . -- a = 0
        fin_cases x with [0,1]
        simp

      . -- a = 1
        fin_cases x with [0,1]
        simp [if_pos]
    have h : ∑' (x : ZMod 2), (pure (1 + x) : PMF (ZMod 2)) a = 1 := by
      simp [pure, PMF.pure, coe_fn, has_coe_to_fun.coe]
      simp_rw [zmod_eq_comm]
      simp
    rw [h]
    simp

  . -- b = 1
    ring_nf
    simp
    have h :
      uniform_2.bind (λ (b : ZMod 2) => pure (b + 0)) = uniform_2 := by simp [pure]
    exact h

/-
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game2 (i.e. guessing the correct bit) is equal to a coin flip.
-/
theorem Game2_uniform : Game2 = uniform_2 := by
  simp [Game2, bind]
  bind_skip_const with x
  bind_skip_const with m
  bind_skip_const with y
  rw [PMF.bind_comm uniform_2]
  simp_rw [PMF.bind_comm uniform_2]
  bind_skip_const with z
  bind_skip_const with ζ
  bind_skip_const with b'
  exact G2_uniform_lemma b'

variable (ε : NNReal)

/-
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and
  therefore ElGamal is, by definition, semantically secure.
-/
theorem elgamal_semantic_security (DDH_G : DDH G g /- g_gen_G -/ q /- G_card_q -/ D ε) :
    PkeSemanticSecurity keygen encrypt A1 A2' ε := by
  simp only [PkeSemanticSecurity]
  rw [SSG_DDH0]
  have h : (((uniform_2) 1) : ennreal) = 1/2 := by
    simp only [uniform_2]
    rw [uniform_zmod_prob 1]
    norm_cast
  rw [<- h]
  rw [<- Game2_uniform]
  rw [<- Game1_Game2]
  rw [Game1_DDH1]
  exact DDH_G

end ElGamal
