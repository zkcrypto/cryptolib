/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key 
  encryption scheme
 -----------------------------------------------------------
-/

import ddh
import pke
import tactics 
import to_mathlib
import uniform

section elgamal

noncomputable theory 

parameters (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
           (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g)
           (h : G) (h_gen_G : ∀ (x : G), x ∈ subgroup.gpowers h)
           (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
           (A_state : Type)

include g_gen_G h_gen_G G_card_q

parameters (A1 : G → pmf (G × G × A_state))
           (A2 : G → G → A_state → pmf (zmod 2))
           
def A2' : G × G → A_state → pmf (zmod 2) := λ (gg : G × G), A2 gg.1 gg.2

-- generates a random opening value
def opening_value : pmf (zmod q) := 
do 
  x ← uniform_zmod q, -- choose from ℤq
  pure (x)

-- commit takes a message M ∈ G and the opening_value ∈ ℤq and returns a commitment, a pair of values 
def commit (M : G) : pmf (G × G) := 
do
  r ← opening_value,
  -- c₀ ← g^r.val -- doesn't work??
  pure (g^r.val, M*h^r.val)

-- Or: Better to create a global parameter?
-- Somehow a commitment must also keep track of M and r...
parameter (r' : zmod q) 

-- variable (r'' : opening_value)

-- Moni Naor - general commitment schemes

#check r'
def commit' (M : G) : pmf (G × G) := return (g^r'.val, M*h^r'.val)

-- Use r as the key in encryption
-- For defining commitment it doesn't matter how r is generated
-- Does matter for computational binding because under the discrete log assumption the adv. gets a g^r' (r' random)
-- In contrast to elgamal encryption commitments are deterministic
-- What if r == 0? Do we have to treat this as a separate case?
def commit'' (M : G) (r : zmod q) : G × G := return (g^r.val, M*h^r.val)

-- `c` is the given commitment, `v` is the pair made up of the message M ∈ G and the opening value, r, provided by the committer at the verification step. Projections are used to access both values of the `v` pair.
-- I think verify needs to reconstruct the commitment from the message and the opening value - but then what does it check *against*?
-- Verify can demonstrate how it *should* work, but it can't actually prove anything on its own... 
-- How do we prove correctness?
-- Makes more sense to think of this as a {0, 1} function - object level rather than meta level
-- Check out EasyCrypt paper - how do they model this?
def verify (c : G × G) (v : G × zmod q) : Prop := -- but this must be `pmf (zmod q)`?
	c = (g^v.2.val, v.1*h^v.2.val)

-- Do we need to do this? `verify` is more definitional then lemma...
lemma verify' (c : G × G) (v : G × zmod q) : c = (g^v.2.val, v.1*h^v.2.val) := sorry


/- 
  -----------------------------------------------------------
  Proof of binding property of ElGamal Commitments
  -----------------------------------------------------------
-/
-- Binding is “perfect” and follows almost directly. Suppose (g^r’,M’h^r’)=(g^r,Mh^r). Since g is a generator, this means r=r’. But then h^r’=h^r, so from M’h^r’=Mh^r we can conclude M=M’. 

-- Given g h ∈ G (provided now by `parameters` above) have the adversary choose some M' ∈ G and r' ∈ ℤq such that c = c'
-- Prove by contradiction?
-- ∀r,r', so no need to worry about uniform selection of r
lemma perfect_binding' {M M' : G} (c : G × G) : M = M' :=
begin
  by_contra h, --???
  sorry
end

lemma perfect_binding (v : G × zmod q) : Prop :=
begin
  have c₀ : g^v.2.val, 
  have c₁ : v.1*h^v.2.val,

  sorry
end



/- 
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

def D (gx gy gz : G) : pmf (zmod 2) := 
do 
  m ← A1 gx,
  b ← uniform_2,
  mb ← pure (if b = 0 then m.1 else m.2.1),
  b' ← A2 gy (gz * mb) m.2.2,
  pure (1 + b + b')

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning the semantic security game (i.e. guessing the correct bit), 
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0. 
-/
theorem SSG_DDH0 : SSG keygen encrypt A1 A2' =  DDH0 G g g_gen_G q G_card_q D :=
begin
  simp only [SSG, DDH0, bind, keygen, encrypt, D],
  simp_rw pmf.bind_bind (uniform_zmod q),
  bind_skip with x,
  simp [pure],
  simp_rw pmf.bind_comm (uniform_zmod q),
  bind_skip with m,
  bind_skip with b,
  bind_skip with y,
  simp only [A2'],
  rw pow_mul g x.val y.val,
end

def Game1 : pmf (zmod 2) :=
do 
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  m ← A1 (g^x.val),
  b ← uniform_2,
  ζ ← (do z ← uniform_zmod q, mb ← pure (if b = 0 then m.1 else m.2.1), pure (g^z.val * mb)),
  b' ← A2 (g^y.val) ζ m.2.2,
  pure (1 + b + b')

def Game2 : pmf (zmod 2) :=
do
  x ← uniform_zmod q,
  y ← uniform_zmod q,
  m ← A1 (g^x.val),
  b ← uniform_2,
  ζ ← (do z ← uniform_zmod q, pure (g^z.val)),
  b' ← A2 (g^y.val) ζ m.2.2,
  pure (1 + b + b')

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game1 (i.e. guessing the correct bit) is equal to the 
  probability of D winning the game DDH1. 
-/
theorem Game1_DDH1 : Game1 = DDH1 G g g_gen_G q G_card_q D := 
begin
  simp only [DDH1, Game1, bind, D],
  bind_skip with x,
  bind_skip with y,
  simp_rw pmf.bind_bind (A1 _),
  conv_rhs {rw pmf.bind_comm (uniform_zmod q)},
  bind_skip with m,
  simp_rw pmf.bind_bind (uniform_zmod q),
  conv_lhs {rw pmf.bind_comm (uniform_2)},
  bind_skip with z,
  conv_rhs {rw pmf.bind_bind (uniform_2)},
  bind_skip with b,
  simp_rw pmf.bind_bind,
  bind_skip with mb,
  simp [pure],
end

lemma exp_bij : 
  function.bijective (λ (z : zmod q), g ^ z.val) := 
begin
  apply (fintype.bijective_iff_surjective_and_card _).mpr,
  split,

  { -- (λ (z : zmod q), g ^ z.val) surjective
    intro gz, 
    have hz := subgroup.mem_gpowers_iff.mp (g_gen_G gz),
    cases hz with z hz,
    cases z,

    { -- Case : z = z' for (z : ℕ)
      let zq := z % q,
      use zq,
      have h1 : (λ (z : zmod q), g ^ z.val) ↑zq = g ^ (zq : zmod q).val := rfl,
      rw h1,
      rw zmod.val_cast_of_lt,
      {
        have goal : gz = g ^ zq := 
        calc
           gz = g ^ int.of_nat z : hz.symm
          ... = g ^ z  : by simp
          ... = g ^ (z % q + q * (z / q)) : by rw nat.mod_add_div z q
          ... = g ^ (z % q) * g ^ (q * (z / q)) : by rw pow_add
          ... = g ^ (z % q) * (g ^ q) ^ (z / q) : by rw pow_mul
          ... = g ^ (z % q) * (g ^ fintype.card G) ^ (z / q) : by rw <- G_card_q
          ... = g ^ (z % q) : by simp [pow_card_eq_one]
          ... = g ^ zq : rfl,
        exact goal.symm, 
      },
      exact nat.mod_lt z _inst_4.out,
    },

    { -- Case : z = - (1 + z') for (z' : ℕ)
      let zq := (q - (z + 1) % q ) % q,
      use zq,
      have h1 : (λ (z : zmod q), g ^ z.val) ↑zq = g ^ (zq : zmod q).val := rfl,
      rw h1,
      rw zmod.val_cast_of_lt,
      {
        have h1 : (z + 1) % q ≤ fintype.card G := 
        begin
          rw G_card_q,
          apply le_of_lt,
          exact nat.mod_lt _ _inst_4.out,
        end,

        have goal : gz = g ^ zq := 
        calc
           gz = g ^ int.neg_succ_of_nat z : hz.symm 
          ... = (g ^ z.succ)⁻¹  : by rw gpow_neg_succ_of_nat
          ... = (g ^ (z + 1))⁻¹ : rfl
          ... = (g ^ ((z + 1) % fintype.card G))⁻¹ : by rw pow_eq_mod_card G g (z + 1)
          ... = (g ^ ((z + 1) % q))⁻¹ : by rw G_card_q
          ... = g ^ (fintype.card G - (z + 1) % q) : inv_pow_eq_card_sub_pow G g _ h1
          ... = g ^ (q - ((z + 1) % q)) : by rw G_card_q
          ... = g ^ ((q - (z + 1) % q) % q
                  + q * ((q - (z + 1) % q) / q)) : by rw nat.mod_add_div
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * g ^ (q * ((q - (z + 1) % q) / q)) : by rw pow_add
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * (g ^ q) ^ ((q - (z + 1) % q) / q) : by rw pow_mul
          ... = g ^ ((q - (z + 1) % q) % q) 
                  * (g ^ fintype.card G) ^ ((q - (z + 1) % q) / q) : by rw <- G_card_q
          ... = g ^ ((q - (z + 1) % q) % q) : by simp [pow_card_eq_one]
          ... = g ^ zq : rfl,
        exact goal.symm, 
      },

      exact nat.mod_lt _ _inst_4.out,  
    },
  },

  { -- fintype.card (zmod q) = fintype.card G
    rw G_card_q,
    exact zmod.card q,
  },
end

lemma exp_mb_bij (mb : G) : function.bijective (λ (z : zmod q), g ^ z.val * mb) := 
begin
  have h : (λ (z : zmod q), g ^ z.val * mb) = 
    ((λ (m : G), (m * mb)) ∘ (λ (z : zmod q), g ^ z.val)) := by simp,
  rw h,
  apply function.bijective.comp,

  { -- (λ (m : G), (m * mb)) bijective
    refine fintype.injective_iff_bijective.mp _,
    intros x a hxa,
    simp at hxa,
    exact hxa,
  },

  { -- (λ (z : zmod q), g ^ z.val) bijective
    exact exp_bij,
  }
end

lemma G1_G2_lemma1 (x : G) (exp : zmod q → G) (exp_bij : function.bijective exp) : 
  ∑' (z : zmod q), ite (x = exp z) (1 : nnreal) 0 = 1 := 
begin
  have inv :=  function.bijective_iff_has_inverse.mp exp_bij,
  cases inv with exp_inv,
  have bij_eq : ∀ (z : zmod q), (x = exp z) = (z = exp_inv x) := 
  begin
    intro z,
    simp,
    split,

    { -- (x = exp z) → (z = exp_inv x)
      intro h,
      have h1 : exp_inv x = exp_inv (exp z) := congr_arg exp_inv h,
      rw inv_h.left z at h1,
      exact h1.symm,
    },

    { -- (z = exp_inv x) → (x = exp z) 
      intro h,
      have h2 : exp z = exp (exp_inv x) := congr_arg exp h,
      rw inv_h.right x at h2,
      exact h2.symm,
    },
  end,
  simp_rw bij_eq,
  simp,
end

lemma G1_G2_lemma2 (mb : G) : 
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val * mb)) =
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val))  := 
begin
  simp [pmf.bind],
  simp_rw uniform_zmod_prob,
  ext,
  simp only [pure, pmf.pure, coe_fn, has_coe_to_fun.coe, nnreal.tsum_mul_left],
  norm_cast,
  simp,
  apply or.intro_left,
  repeat {rw G1_G2_lemma1 x},
  exact exp_bij,
  exact exp_mb_bij mb,
end
 
lemma G1_G2_lemma3 (m : pmf G) : 
  m.bind (λ (mb : G), (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val * mb))) =
  (uniform_zmod q).bind (λ (z : zmod q), pure (g^z.val)) := 
begin
  simp_rw G1_G2_lemma2 _,
  bind_skip_const with m,
  congr,
end

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game1 (i.e. guessing the correct bit) is equal to the 
  probability of the attacker winning Game2.
-/
theorem Game1_Game2 : Game1 = Game2 := 
begin
  simp only [Game1, Game2],
  bind_skip with x,
  bind_skip with y, 
  bind_skip with m,
  bind_skip with b,
  simp [bind, -pmf.bind_pure, -pmf.bind_bind],
  simp_rw pmf.bind_comm (uniform_zmod q),
  rw G1_G2_lemma3,
end

lemma G2_uniform_lemma (b' : zmod 2) : 
uniform_2.bind (λ (b : zmod 2), pure (1 + b + b')) = uniform_2 :=
begin
  fin_cases b' with [0,1],

  { -- b = 0
    ring_nf,
    ext,
    simp [uniform_2],
    rw uniform_zmod_prob a,
    simp_rw uniform_zmod_prob,
    simp [nnreal.tsum_mul_left],
    have zmod_eq_comm : ∀ (x : zmod 2), (a = 1 + x) = (x = 1 + a) := 
    begin
      intro x,
      fin_cases a with [0,1],

      { -- a = 0
        fin_cases x with [0,1],
        simp,
        ring_nf,
      }, 

      { -- a = 1
        fin_cases x with [0,1],
        simp [if_pos],
        ring_nf,
      },
    end,
    have h : ∑' (x : zmod 2), (pure (1 + x) : pmf (zmod 2)) a = 1 := 
    begin
      simp [pure, pmf.pure, coe_fn, has_coe_to_fun.coe],
      simp_rw zmod_eq_comm,
      simp,
    end,
    rw h,
    simp,
  },

  { -- b = 1
    ring_nf,
    have h : 
      uniform_2.bind (λ (b : zmod 2), pure (b + 0)) = uniform_2 := by simp [pure],
    exact h,
  },
end

/- 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game2 (i.e. guessing the correct bit) is equal to a coin flip.
-/
theorem Game2_uniform : Game2 = uniform_2 :=
begin
  simp [Game2, bind],
  bind_skip_const with x,
  bind_skip_const with m,
  bind_skip_const with y,
  rw pmf.bind_comm uniform_2,
  simp_rw pmf.bind_comm uniform_2,
  bind_skip_const with z,
  bind_skip_const with ζ,
  bind_skip_const with b',
  exact G2_uniform_lemma b',
end

parameters (ε : nnreal) 

/- 
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in 
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and 
  therefore ElGamal is, by definition, semantically secure.
-/
theorem elgamal_semantic_security (DDH_G : DDH G g g_gen_G q G_card_q D ε) : 
  pke_semantic_security keygen encrypt A1 A2' ε := 
begin
  simp only [pke_semantic_security],
  rw SSG_DDH0,
  have h : (((uniform_2) 1) : ℝ) = 1/2 := 
  begin
    simp only [uniform_2],
    rw uniform_zmod_prob 1,
    norm_cast,
  end,
  rw <- h,
  rw <- Game2_uniform,
  rw <- Game1_Game2,
  rw Game1_DDH1,
  exact DDH_G,
end

end elgamal
