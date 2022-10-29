/-
  Section 8 : The Salsa20 hash function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.doubleround
import salsa20.littleendian

open words
open littleendian
open doubleround

namespace salsa20

-- x is a 64-byte sequence
variable x : vector (bitvec byte_len) 64

-- x₀ = littleendian(x[0], x[1], x[2], x[3])
def x₀ : bitvec word_len := littleendian ([(x.nth 0), (x.nth 1), (x.nth 2), (x.nth 3)].to_vec_of_bitvec byte_len 4)

-- x₁ = littleendian(x[4], x[5], x[6], x[7])
def x₁ : bitvec word_len := littleendian ([(x.nth 4), (x.nth 5), (x.nth 6), (x.nth 7)].to_vec_of_bitvec byte_len 4)

-- x₂ = littleendian(x[8], x[9], x[10], x[11])
def x₂ : bitvec word_len := littleendian ([(x.nth 8), (x.nth 9), (x.nth 10), (x.nth 11)].to_vec_of_bitvec byte_len 4)

-- x₃ = littleendian(x[12], x[13], x[14], x[15])
def x₃ : bitvec word_len := littleendian ([(x.nth 12), (x.nth 13), (x.nth 14), (x.nth 15)].to_vec_of_bitvec byte_len 4)

-- x₄ = littleendian(x[16], x[17], x[18], x[19])
def x₄ : bitvec word_len := littleendian ([(x.nth 16), (x.nth 17), (x.nth 18), (x.nth 19)].to_vec_of_bitvec byte_len 4)

-- x₅ = littleendian(x[20], x[21], x[22], x[23])
def x₅ : bitvec word_len := littleendian ([(x.nth 20), (x.nth 21), (x.nth 22), (x.nth 23)].to_vec_of_bitvec byte_len 4)

-- x₆ = littleendian(x[24], x[25], x[26], x[27])
def x₆ : bitvec word_len := littleendian ([(x.nth 24), (x.nth 25), (x.nth 26), (x.nth 27)].to_vec_of_bitvec byte_len 4)

-- x₇ = littleendian(x[28], x[29], x[30], x[31])
def x₇ : bitvec word_len := littleendian ([(x.nth 28), (x.nth 29), (x.nth 30), (x.nth 31)].to_vec_of_bitvec byte_len 4)

-- x₈ = littleendian(x[32], x[33], x[34], x[35])
def x₈ : bitvec word_len := littleendian ([(x.nth 32), (x.nth 33), (x.nth 34), (x.nth 35)].to_vec_of_bitvec byte_len 4)

-- x₉ = littleendian(x[36], x[37], x[38], x[39])
def x₉ : bitvec word_len := littleendian ([(x.nth 36), (x.nth 37), (x.nth 38), (x.nth 39)].to_vec_of_bitvec byte_len 4)

-- x₁₀ = littleendian(x[40], x[41], x[42], x[43])
def x₁₀ : bitvec word_len := littleendian ([(x.nth 40), (x.nth 41), (x.nth 42), (x.nth 43)].to_vec_of_bitvec byte_len 4)

-- x₁₁ = littleendian(x[44], x[45], x[46], x[47])
def x₁₁ : bitvec word_len := littleendian ([(x.nth 44), (x.nth 45), (x.nth 46), (x.nth 47)].to_vec_of_bitvec byte_len 4)

-- x₁₂ = littleendian(x[48], x[49], x[50], x[51])
def x₁₂ : bitvec word_len := littleendian ([(x.nth 48), (x.nth 49), (x.nth 50), (x.nth 51)].to_vec_of_bitvec byte_len 4)

-- x₁₃ = littleendian(x[52], x[53], x[54], x[55])
def x₁₃ : bitvec word_len := littleendian ([(x.nth 52), (x.nth 53), (x.nth 54), (x.nth 55)].to_vec_of_bitvec byte_len 4)

-- x₁₄ = littleendian(x[56], x[57], x[58], x[59])
def x₁₄ : bitvec word_len := littleendian ([(x.nth 56), (x.nth 57), (x.nth 58), (x.nth 59)].to_vec_of_bitvec byte_len 4)

-- x₁₅ = littleendian(x[60], x[61], x[62], x[63])
def x₁₅ : bitvec word_len := littleendian ([(x.nth 60), (x.nth 61), (x.nth 62), (x.nth 63)].to_vec_of_bitvec byte_len 4)

-- Doubleround to the n power (doubleround n times)
def doubleround_exp_n : 
  ℕ → vector (bitvec word_len) 64 → vector (bitvec word_len) 64
| 0 v := v
| (n+1) v := do
    let round := 
      doubleround (
        [
          (v.nth 0), (v.nth 1), (v.nth 2), (v.nth 3), (v.nth 4), (v.nth 5), (v.nth 6), (v.nth 7),
          (v.nth 8), (v.nth 9), (v.nth 10), (v.nth 11), (v.nth 12), (v.nth 13), (v.nth 14), (v.nth 15)
        ]
         .to_vec_of_bitvec word_len 16),

    doubleround_exp_n (n) (list.to_vec_of_bitvec word_len 64 round.to_list)

-- (z₀, z₁, ... , z₁₅) = doubleround¹⁰(x₀, x₁, ... , x₁₅)
def z : vector (bitvec word_len) 64 := 
  doubleround_exp_n 10 (list.to_vec_of_bitvec word_len 64 [
    x₀ x, x₁ x, x₂ x, x₃ x, x₄ x, x₅ x, x₆ x, x₇ x, 
    x₈ x, x₉ x,x₁₀ x, x₁₁ x, x₁₂ x, x₁₃ x, x₁₄ x,x₁₅ x
  ])
  
def z₀ : bitvec word_len := (z x).nth 0
def z₁ : bitvec word_len := (z x).nth 1
def z₂ : bitvec word_len := (z x).nth 2
def z₃ : bitvec word_len := (z x).nth 3
def z₄ : bitvec word_len := (z x).nth 4
def z₅ : bitvec word_len := (z x).nth 5
def z₆ : bitvec word_len := (z x).nth 6
def z₇ : bitvec word_len := (z x).nth 7
def z₈ : bitvec word_len := (z x).nth 8
def z₉ : bitvec word_len := (z x).nth 9
def z₁₀ : bitvec word_len := (z x).nth 10
def z₁₁ : bitvec word_len := (z x).nth 11
def z₁₂ : bitvec word_len := (z x).nth 12
def z₁₃ : bitvec word_len := (z x).nth 13
def z₁₄ : bitvec word_len := (z x).nth 14
def z₁₅ : bitvec word_len := (z x).nth 15

-- Salsa20(x) is the concatenation of 
-- littleendian⁻¹(z₀ + x₀),
-- littleendian⁻¹(z₁ + x₁),
-- littleendian⁻¹(z₂ + x₂),
-- ...
-- littleendian⁻¹(z₁₅ + x₁₅).
def salsa20 : vector (bitvec byte_len) 64 := do
  let s₀ := littleendian_inv ((z₀ x) + (x₀ x)),
  let s₁ := littleendian_inv ((z₁ x) + (x₁ x)),
  let s₂ := littleendian_inv ((z₂ x) + (x₂ x)),
  let s₃ := littleendian_inv ((z₃ x) + (x₃ x)),
  let s₄ := littleendian_inv ((z₄ x) + (x₄ x)),
  let s₅ := littleendian_inv ((z₅ x) + (x₅ x)),
  let s₆ := littleendian_inv ((z₆ x) + (x₆ x)),
  let s₇ := littleendian_inv ((z₇ x) + (x₇ x)),
  let s₈ := littleendian_inv ((z₈ x) + (x₈ x)),
  let s₉ := littleendian_inv ((z₉ x) + (x₉ x)),
  let s₁₀ := littleendian_inv ((z₁₀ x) + (x₁₀ x)),
  let s₁₁ := littleendian_inv ((z₁₁ x) + (x₁₁ x)),
  let s₁₂ := littleendian_inv ((z₁₂ x) + (x₁₂ x)),
  let s₁₃ := littleendian_inv ((z₁₃ x) + (x₁₃ x)),
  let s₁₄ := littleendian_inv ((z₁₄ x) + (x₁₄ x)),
  let s₁₅ := littleendian_inv ((z₁₅ x) + (x₁₅ x)),

  (((((((((((((((s₀.append s₁).append s₂).append s₃).append s₄).append s₅).append s₆).append s₇)
  .append s₈).append s₉).append s₁₀).append s₁₁).append s₁₂).append s₁₃).append s₁₄).append s₁₅)

lemma salsa20_zero : salsa20
  (list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]) = list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ] :=
  begin
    -- not trivial with our current definitions
    sorry,
  end

lemma salsa_20_output_len_is_always_64 (x' : (vector (bitvec byte_len) 64)) : (salsa20.salsa20 x').length = 64 :=
begin
  refl,
end

end salsa20
