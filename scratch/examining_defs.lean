import uniform
import pke
import tactics

variables (G : Type) [fintype G] [group G] [decidable_eq G]
variable g : G

-- `uniform_grp : pmf G` relies on the `pmf` function `of_multiset` to produce a `pmf` from a multiset ("`multiset α` is the quotient of `list α` by list permutation. The result is a type of finite sets with duplicates allowed." - from probability_mass_function.lean) and a proof that the multiset is not equal to 0. 

#check pmf.of_multiset
#check multiset
#check finset
#check G -- A type
#check fintype G -- A finite type
#check fintype.elems G -- A finset of elements of G - the finite set of elements of G
#check (fintype.elems G).val -- A multiset of G

#check uniform_grp G  -- Produces a PMF G which can be applied to an element of G
#check uniform_grp G g -- returns an `nnreal` (non-negative reals) which should be `1/|G|`, according to `uniform_grp_prob` in uniform.lean

#check SSG -- Relies on monadic style binds to produce a pmf distribution for the given crypto system

#check pke_semantic_security

#check pmf.pure_bind

noncomputable
def p1: pmf (zmod 5) :=
do 
  x ← uniform_zmod 5,
  y ← uniform_zmod 5,
  pure (x + y)

noncomputable
def p2: pmf (zmod 5) :=
do 
  x ← uniform_zmod 5,
  y ← uniform_zmod 5,
  pure (y + x)

def p2' := 3 

#check p2'

example : p1 = p2 :=
begin
  simp [p1, p2], 
  bind_skip with x, 
  bind_skip with y,
  simp_rw add_comm,
end

example : p1 = p2' :=
begin

end