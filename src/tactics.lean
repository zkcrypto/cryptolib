import probability.probability_mass_function.basic
import probability.probability_mass_function.monad

variables {α β : Type}

lemma bind_skip' (p : pmf α) (f g : α → pmf β) :
  (∀ (a : α), f a = g a) → p.bind f = p.bind g :=
begin
  intro ha,
  ext,
  simp only [pmf.bind_apply, nnreal.coe_eq],
  simp_rw ha,
end

lemma bind_skip_const' (pa : pmf α) (pb : pmf β) (f : α → pmf β) :
  (∀ (a : α), f a = pb) → pa.bind f = pb :=
begin
  intro ha,
  ext,
  simp only [pmf.bind_apply, nnreal.coe_eq],
  simp_rw ha,
  simp [ennreal.tsum_mul_right],
end

setup_tactic_parser
meta def tactic.interactive.bind_skip  (x : parse (tk "with" *> ident)?) : tactic unit :=
do `[apply bind_skip'],
  let a := x.get_or_else `_,
  tactic.interactive.intro a

meta def tactic.interactive.bind_skip_const  (x : parse (tk "with" *> ident)?) : tactic unit :=
do `[apply bind_skip_const'],
  let a := x.get_or_else `_,
  tactic.interactive.intro a
