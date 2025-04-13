/-
From the [Lean Reference Manual section 3.3](https://leanprover.github.io/reference/expressions.html)
-/

import data.int.basic

universe u

def ex1 (x y z : ℕ) : ℕ := x + y + z

#check ex1 1 2 3
#eval ex1 1 2 3

def id1 (α : Type) (x : α) : α := x

#check id1 3 -- doesn't work because α must be explicitly inserted
#check id1 nat 3
#check id1 _ 3

def id2 {α : Type u} (x : α) : α := x

#check id2 3
#check id2 ℕ 3 -- doens't work because ℕ can't explicitly be inserted (without @ annotation)
#check @id2 ℕ 3
#check (id2 : ℕ → ℕ)

#check s ∪ ↑[3, 2]

def id3 {{α : Type u}} (x : α) : α := x -- weakly inserted implicit argument

#check id3 3
#check @id3 ℕ 3
#check (id3 : Π α : Type, α → α)

def id4 {α : Type u} {a : α} (x : α) : α := x

#check id4 2
#check @id4 ℕ 2 3

class cls := (val : ℕ)
instance cls_five : cls := ⟨5⟩

def ex2 [c : cls] : ℕ := c.val

example : ex2 = 5 := rfl

def ex2a [cls] : ℕ := ex2

example : ex2a = 5 := rfl

def ex3 (x : ℕ := 5) := x

#check ex3 2
#check ex3
example : ex3 = 5 := rfl

meta def ex_tac : tactic unit := tactic.refine ``(5)

def ex4 (x : ℕ . ex_tac) := x

example : ex4 = 5 := rfl


variable (p : ℕ)
variable (a : ℤ)

section ptest

parameter (l : ℤ)

end ptest

def foo : (ℕ → ℕ) → ℕ := λ f, f 0
def double (x : ℕ) : ℕ := x + x
theorem test : a + 0 = a := add_zero a

#check foo
#check double
#check test


