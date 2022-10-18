/-
  Section 3 : The quarterround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words

-- z₁ = y₁ ⊕ ((y₀ + y₃) <<< 7)
def z₁ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 1) (rotate7 (nat_as_bitvec (mod_as_nat (sum_as_mod (y.nth 0) (y.nth 3)))))

-- z₂ = y₂ ⊕ ((z₁ + y₀) <<< 9)
def z₂ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 2) (rotate9 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₁ y) (y.nth 0)))))

-- z₃ = y₃ ⊕ ((z₂ + z₁) <<< 13)
def z₃ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 3) (rotate13 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₂ y) (z₁ y)))))

-- z₀ = y₀ ⊕ ((z₃ + z₂) <<< 18)
def z₀ (y : vector (bitvec word_len) 4) : bitvec word_len := 
  bitvec.xor (y.nth 0) (rotate18 (nat_as_bitvec (mod_as_nat (sum_as_mod (z₃ y) (z₂ y)))))

-- quarterround(y = y0, y1, y2, y3) = (z0, z1, z2, z3)
def quarterround (y : vector (bitvec word_len) 4) : vector (bitvec word_len) 4 :=
    [z₀ y, z₁ y, z₂ y, z₃ y].to_vec_of_bitvec word_len 4

-- quarterround(0, 0, 0, 0) = [0, 0, 0, 0]
lemma quarterround_zero : 
  (quarterround ([0, 0, 0, 0].to_vec_of_bitvec word_len 4)).to_list = [0, 0, 0, 0] := rfl

-- TODO: The whole quarterround function is invertible
def quarterround_inv : list (bitvec word_len) :=
  do 
    sorry

-- Examples from the spec

-- example 1
namespace example1

def y : (vector (bitvec word_len) 4) := 
  [0x00000000, 0x00000000, 0x00000000, 0x00000000].to_vec_of_bitvec word_len 4

example : (z₁ y).to_nat = 0x00000000 := by refl
example : (z₂ y).to_nat = 0x00000000 := by refl
example : (z₃ y).to_nat = 0x00000000 := by refl
example : (z₀ y).to_nat = 0x00000000 := by refl

end example1

-- example 2
namespace example2

def y : (vector (bitvec word_len) 4) := 
  [0x00000001, 0x00000000, 0x00000000, 0x00000000].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0x00000080
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0x00010200
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x20500000
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0x08008145
#eval ((quarterround y).nth 0).to_nat

end example2

-- example 3
namespace example3

def y : (vector (bitvec word_len) 4) := 
  [0x00000000, 0x00000001, 0x00000000, 0x00000000].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0x00000001
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0x00000200
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x00402000
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0x88000100
#eval ((quarterround y).head).to_nat

end example3

-- example 4
namespace example4

def y0 : bitvec word_len := 0x00000000
def y1 : bitvec word_len := 0x00000000
def y2 : bitvec word_len := 0x00000001
def y3 : bitvec word_len := 0x00000000

def y : (vector (bitvec word_len) 4) := 
  [0x00000000, 0x00000000, 0x00000001, 0x00000000].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0x00000000
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0x00000001
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x00002000
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0x80040000
#eval ((quarterround y).head).to_nat

end example4

-- example 5
namespace example5

def y : (vector (bitvec word_len) 4) := 
  [0x00000000, 0x00000000, 0x00000000, 0x00000001].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0x00000080
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0x00010000
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x20100001
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0x00048044
#eval ((quarterround y).head).to_nat

end example5

-- example 6
namespace example6

def y : (vector (bitvec word_len) 4) := 
  [0xe7e8c006, 0xc4f9417d, 0x6479b4b2, 0x68c67137].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0x9361dfd5
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0xf1460244
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x948541a3
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0xe876d72b
#eval ((quarterround y).head).to_nat

end example6

-- example 7
namespace example7

def y : (vector (bitvec word_len) 4) := 
  [0xd3917c5b, 0x55f1c407, 0x52a58a7a, 0x8f887a3b].to_vec_of_bitvec word_len 4

#eval (z₁ y).to_nat
#eval 0xd90a8f36
#eval ((quarterround y).nth 1).to_nat

#eval (z₂ y).to_nat
#eval 0x6ab2a923
#eval ((quarterround y).nth 2).to_nat

#eval (z₃ y).to_nat
#eval 0x2883524c
#eval ((quarterround y).nth 3).to_nat

#eval (z₀ y).to_nat
#eval 0x3e2f308c
#eval ((quarterround y).head).to_nat

end example7
