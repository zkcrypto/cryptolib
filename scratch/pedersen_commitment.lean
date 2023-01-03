/-
Pedersen Commitments - Theorem 3.1: https://link.springer.com/content/pdf/10.1007/3-540-46766-1_9.pdf#page=3

For any s ∈ ℤq for randomly uniformly chosen t ∈ ℤq, E(s,t) is uniformly distributed in Gq.

If s,s' ∈ ℤq satisfies s ≠ s' and E(s,t) = E(s',t'), then t ≠ t' mod q and

log g h = {(s - s') / (t' - t)} mod q
-/

import uniform
noncomputable theory

variables (q₁ : ℕ) [fact (0 < q₁)] -- There must be a better way to do this... 
          -- (zq₁' : ∀ (x : ℕ) [fact (x < q₁)], x ∈ (uniform_zmod q₁)) -- can't do this because although uniform_zmod is meant to represent a cyclic group ℤq, it's actually a pmf
def zq₁ : pmf (zmod q₁) := uniform_zmod q₁


variables (G : Type) [fintype G] [comm_group G] [decidable_eq G] 
          (g : G) (g_gen_G : ∀ (x : G), x ∈ subgroup.gpowers g)
          (q : ℕ) [fact (0 < q)] (G_card_q : fintype.card G = q) 
          (m m': zmod q)

include g_gen_G G_card_q

/-
Commitment phase:
1. R samples h ∈ G and sends h to C
2. C samples the opening value d ∈ ℤq and computes c = g^d * h^m and sends to R

Verification phase:
1. C sends m and d to R
2. R checks whether g^d * h^m matches c (from C) and either accepts or rejects
-/


def gen: pmf G :=
do 
  x ← uniform_zmod q, -- This should be a uniformly chosen element of ℤq
  pure(g^x.val) -- In EasyCrypt they return an h because gen is a callable function

#check gen

def commit (h : G) (m : zmod q) : (G × zmod q) := -- but should h : pmf G? -- : G × zmod q?
do
  d ← uniform_zmod q,
  -- pure (g^d.val * h^m.val) -- This is fine?
  c ← pure(g^d.val * h^m.val),
  pure (c × d)

def verify (h : G) (m : zmod q) (c : G) (d : zmod q) : Prop :=
do 
  c' ← g^d.val * h^m.val,
  pure (c == c')

#check G_card_q

def E_s_t (s : zmod q): pmf G := 
do
  t ← uniform_zmod q,
  pure (g^s.val * h^t.val)


-- Definition of the discrete log assumption
-- Definition of computationally binding commitment - an adversary who can break this will provide an adversary that can compute the discrete log
-- Game-like reduction for binding => Discrete log experiment (Katz and Lindell)
-- Characterizing a hiding game - adversary 
-- Hiding is a "perfect statistical property"
