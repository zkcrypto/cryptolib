/-
  Section 9 : The Salsa20 expansion function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.salsa20

open words

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

-- If k₀, k₁, n are 16-byte sequences then Salsa20ₖ₀,ₖ₁(n) = Salsa20 (σ₀, k₀, σ1₁, n, σ₂, k₁, σ₃)
def salsa20_expansion_v1 (k₀ : vector (bitvec byte_len) 16)
  (k₁ : vector (bitvec byte_len) 16) (n : vector (bitvec byte_len) 16) : vector (bitvec byte_len) 64 :=
    salsa20.salsa20 
      ((((((σ₀.append k₀).append σ₁).append n).append σ₂).append k₁).append σ₃)

-- If k, n are 16-byte sequences then Salsa20k(n) = Salsa20(τ₀, k, τ₁, n, τ₂, k, τ₃)
def salsa20_expansion_v2 (k : vector (bitvec byte_len) 16)
  (n : vector (bitvec byte_len) 16) : vector (bitvec byte_len) 64 :=
    salsa20.salsa20 
      ((((((τ₀.append k).append τ₁).append n).append τ₂).append k).append τ₃)

-- TODO:
-- The constants σ₀ σ₁ σ₂ σ₃ and τ₀ τ₁ τ₂ τ₃ are "expand 32-byte k" 
-- and "expand 16-byte k" in ASCII

end salsa20_expansion
