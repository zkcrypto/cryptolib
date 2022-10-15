/-
  Section 9 : The Salsa20 expansion function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.salsa20

namespace salsa20_expansion

-- σ₀ = (101, 120, 112, 97)
def σ₀ : vector (bitvec byte_len) 4 := ([101, 120, 112, 97].to_vec_of_bitvec byte_len 4)

-- σ₁ = (110, 100, 32, 51)
def σ₁ : vector (bitvec byte_len) 4 := ([110, 100, 32, 51].to_vec_of_bitvec byte_len 4)

-- σ₂ = (50, 45, 98, 121)
def σ₂ : vector (bitvec byte_len) 4 := ([50, 45, 98, 121].to_vec_of_bitvec byte_len 4)

-- σ₃ = (116, 101, 32, 107)
def σ₃ : vector (bitvec byte_len) 4 := ([116, 101, 32, 107].to_vec_of_bitvec byte_len 4)

-- τ₀ = (101, 120, 112, 97)
def τ₀ : vector (bitvec byte_len) 4 := ([101, 120, 112, 97].to_vec_of_bitvec byte_len 4)

-- τ₁ = (110, 100, 32, 49)
def τ₁ : vector (bitvec byte_len) 4 := ([110, 100, 32, 49].to_vec_of_bitvec byte_len 4)

-- τ₂ = (54, 45, 98, 121)
def τ₂ : vector (bitvec byte_len) 4 := ([54, 45, 98, 121].to_vec_of_bitvec byte_len 4)

-- τ₃ = (116, 101, 32, 107)
def τ₃ : vector (bitvec byte_len) 4 := ([116, 101, 32, 107].to_vec_of_bitvec byte_len 4)

-- If k₀, k₁, n are 16-byte sequences then Salsa20ₖ₀,ₖ₁(n) =
-- Salsa20 (σ₀, k₀, σ1₁, n, σ₂, k₁, σ₃)
def salsa20_expansion_v1 (k₀ : vector (bitvec byte_len) 16)
  (k₁ : vector (bitvec byte_len) 16) (n : vector (bitvec byte_len) 16) : vector (bitvec byte_len) 64 :=
    salsa20.salsa20 
      ((((((σ₀.append k₀).append σ₁).append n).append σ₂).append k₁).append σ₃)

-- If k, n are 16-byte sequences then Salsa20k(n) =
-- Salsa20(τ₀, k, τ₁, n, τ₂, k, τ₃)
def salsa20_expansion_v2 (k : vector (bitvec byte_len) 16)
  (n : vector (bitvec byte_len) 16) : vector (bitvec byte_len) 64 :=
    salsa20.salsa20 
      ((((((τ₀.append k).append τ₁).append n).append τ₂).append k).append τ₃)

namespace examples

-- k₀ = (1, 2, 3, 4, 5, ... , 16)
def test_k₀ : vector (bitvec byte_len) 16 :=
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16].to_vec_of_bitvec byte_len 16)

-- k₁ = (201, 202, 203, 204, 205, ... , 216)
def test_k₁ : vector (bitvec byte_len) 16 :=
  ([201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216].to_vec_of_bitvec byte_len 16)

-- n = (101, 102, 103, 104, 105, ... , 116)
def test_n : vector (bitvec byte_len) 16 :=
  ([101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116].to_vec_of_bitvec byte_len 16)

def res1 : list (bitvec byte_len) := [
  69, 37, 68, 39, 41, 15, 107, 193, 255, 139, 122, 6, 170, 233, 217, 98,
  89, 144, 182, 106, 21, 51, 200, 65, 239, 49, 222, 34, 215, 114, 40, 126,
  104, 197, 7, 225, 197, 153, 31, 2, 102, 78, 76, 176, 84, 245, 246, 184,
  177, 160, 133, 130, 6, 72, 149, 119, 192, 195, 132, 236, 234, 103, 246, 74
]

def res2 : list(bitvec byte_len) := [
  39, 173, 46, 248, 30, 200, 82, 17, 48, 67, 254, 239, 37, 18, 13, 247,
  241, 200, 61, 144, 10, 55, 50, 185, 6, 47, 246, 253, 143, 86, 187, 225,
  134, 85, 110, 246, 161, 163, 43, 235, 231, 94, 171, 51, 145, 214, 112, 29,
  14, 232, 5, 16, 151, 140, 183, 141, 171, 9, 122, 181, 104, 182, 177, 193
]

#eval if res1 = (salsa20_expansion_v1 test_k₀ test_k₁ test_n).to_list then tt else ff

#eval if res2 = (salsa20_expansion_v2 test_k₀ test_n).to_list then tt else ff


end examples

-- TODO:
-- The constants σ₀ σ₁ σ₂ σ₃ and τ₀ τ₁ τ₂ τ₃ are "expand 32-byte k" 
-- and "expand 16-byte k" in ASCII

end salsa20_expansion
