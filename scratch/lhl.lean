import to_mathlib

-- From Regev p. 33
/- 

Claim 5.3: Let G be some finite Abelian group and let l be some integer. For any l elements g₁,...,gₗ  ∈ G consider the statistical distance between the uniform distribution on G and the distribution given by the sum of a random subset of g₁,...,gₗ. Then the expectation of this statistical distance over a uniform choice of g₁,...,gₗ ∈ G is at most (∣G∣/2ˡ)^(1/2) In particular, the probability that this statistical distance is more than (∣G∣/2ˡ)^1/4 is at most (∣G∣/2ˡ)^1/4. 

-/

/-
variables (G : Type) [fintype G] [group G] [decidable_eq G]

noncomputable theory 

def uniform_bitvec (n : ℕ) : pmf (bitvec n) := 
  pmf.of_multiset (bitvec.fintype n).elems.val (bitvec.multiset_ne_zero n)

-/
noncomputable theory 

variables (G : Type) [fintype G] [add_comm_group G] 
          (l : ℕ)

def elements : pmf G := 
  pmf.of_multiset (fintype.elems G).val (group.multiset_ne_zero G)