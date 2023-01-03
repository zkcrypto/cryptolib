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

def id3 {{α : Type u}} (x : α) : α := x

#check id3 3
#check @id3 ℕ 3
#check (id3 : Π α : Type, α → α)

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
