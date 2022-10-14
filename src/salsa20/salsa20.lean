/-
  Section 8 : The Salsa20 hash function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.doubleround
import salsa20.littleendian

namespace salsa20

-- x is a 64-byte sequence
variable x : vector (bitvec byte_len) 64

-- x0 = littleendian(x[0], x[1], x[2], x[3])
def x0 : bitvec word_len := littleendian 
  ([
    (x.nth 0),
    (x.nth 1),
    (x.nth 2),
    (x.nth 3)
  ].to_vec_of_bitvec byte_len 4)

-- x1 = littleendian(x[4], x[5], x[6], x[7])
def x1 : bitvec word_len := littleendian 
  ([
    (x.nth 4), 
    (x.nth 5),
    (x.nth 6),
    (x.nth 7)
  ].to_vec_of_bitvec byte_len 4)

-- x2 = littleendian(x[8], x[9], x[10], x[11])
def x2 : bitvec word_len := littleendian 
  ([
    (x.nth 8),
    (x.nth 9),
    (x.nth 10),
    (x.nth 11)
  ].to_vec_of_bitvec byte_len 4)

-- x3 = littleendian(x[12], x[13], x[14], x[15])
def x3 : bitvec word_len := littleendian 
  ([
    (x.nth 12),
    (x.nth 13),
    (x.nth 14),
    (x.nth 15)
  ].to_vec_of_bitvec byte_len 4)

-- x4 = littleendian(x[16], x[17], x[18], x[19])
def x4 : bitvec word_len := littleendian 
  ([
    (x.nth 16),
    (x.nth 17),
    (x.nth 18),
    (x.nth 19)
  ].to_vec_of_bitvec byte_len 4)

-- x5 = littleendian(x[20], x[21], x[22], x[23])
def x5 : bitvec word_len := littleendian 
  ([
    (x.nth 20),
    (x.nth 21),
    (x.nth 22),
    (x.nth 23)
  ].to_vec_of_bitvec byte_len 4)

-- x6 = littleendian(x[24], x[25], x[26], x[27])
def x6 : bitvec word_len := littleendian 
  ([
    (x.nth 24),
    (x.nth 25),
    (x.nth 26),
    (x.nth 27)
  ].to_vec_of_bitvec byte_len 4)

-- x7 = littleendian(x[28], x[29], x[30], x[31])
def x7 : bitvec word_len := littleendian 
  ([
    (x.nth 28),
    (x.nth 29),
    (x.nth 30),
    (x.nth 31)
  ].to_vec_of_bitvec byte_len 4)

-- x8 = littleendian(x[32], x[33], x[34], x[35])
def x8 : bitvec word_len := littleendian 
  ([
    (x.nth 32),
    (x.nth 33),
    (x.nth 34),
    (x.nth 35)
  ].to_vec_of_bitvec byte_len 4)

-- x9 = littleendian(x[36], x[37], x[38], x[39])
def x9 : bitvec word_len := littleendian 
  ([
    (x.nth 36),
    (x.nth 37),
    (x.nth 38),
    (x.nth 39)
  ].to_vec_of_bitvec byte_len 4)

-- x10 = littleendian(x[40], x[41], x[42], x[43])
def x10 : bitvec word_len := littleendian 
  ([
    (x.nth 40),
    (x.nth 41),
    (x.nth 42),
    (x.nth 43)
  ].to_vec_of_bitvec byte_len 4)

-- x11 = littleendian(x[44], x[45], x[46], x[47])
def x11 : bitvec word_len := littleendian 
  ([
    (x.nth 44),
    (x.nth 45),
    (x.nth 46),
    (x.nth 47)
  ].to_vec_of_bitvec byte_len 4)

-- x12 = littleendian(x[48], x[49], x[50], x[51])
def x12 : bitvec word_len := littleendian 
  ([
    (x.nth 48),
    (x.nth 49),
    (x.nth 50),
    (x.nth 51)
  ].to_vec_of_bitvec byte_len 4)

-- x13 = littleendian(x[52], x[53], x[54], x[55])
def x13 : bitvec word_len := littleendian 
  ([
    (x.nth 52),
    (x.nth 53),
    (x.nth 54),
    (x.nth 55)
  ].to_vec_of_bitvec byte_len 4)

-- x14 = littleendian(x[56], x[57], x[58], x[59])
def x14 : bitvec word_len := littleendian 
  ([
    (x.nth 56),
    (x.nth 57),
    (x.nth 58),
    (x.nth 59)
  ].to_vec_of_bitvec byte_len 4)

-- x15 = littleendian(x[60], x[61], x[62], x[63])
def x15 : bitvec word_len := littleendian 
  ([
    (x.nth 60),
    (x.nth 61),
    (x.nth 62),
    (x.nth 63)
  ].to_vec_of_bitvec byte_len 4)

-- Doubleround to the n power (doubleround n times)
def doubleround_exp_n : 
  ℕ → vector (bitvec word_len) 64 → vector (bitvec word_len) 64
| 0 l := l
| (n+1) l := do {
    let w0 := (l.nth 0),
    let w1 := (l.nth 1),
    let w2 := (l.nth 2),
    let w3 := (l.nth 3),
    let w4 := (l.nth 4),
    let w5 := (l.nth 5),
    let w6 := (l.nth 6),
    let w7 := (l.nth 7),
    let w8 := (l.nth 8),
    let w9 := (l.nth 9),
    let w10 := (l.nth 10),
    let w11 := (l.nth 11),
    let w12 := (l.nth 12),
    let w13 := (l.nth 13),
    let w14 := (l.nth 14),
    let w15 := (l.nth 15),

    let round := doubleround w0 w1 w2 w3 w4 w5 w6 w7 w8
      w9 w10 w11 w12 w13 w14 w15,

    doubleround_exp_n (n) (list.to_vec_of_bitvec word_len 64 round)
}

-- (z0, z1, . . . , z15) = doubleround¹⁰(x0, x1, . . . , x15)
def z : vector (bitvec word_len) 64 := 
  doubleround_exp_n 10 (list.to_vec_of_bitvec word_len 64 [
    x0 x,
    x1 x,
    x2 x,
    x3 x,
    x4 x,
    x5 x,
    x6 x,
    x7 x,
    x8 x,
    x9 x,
    x10 x,
    x11 x,
    x12 x,
    x13 x,
    x14 x,
    x15 x
  ])
  
def z0 : bitvec word_len := (z x).nth 0
def z1 : bitvec word_len := (z x).nth 1
def z2 : bitvec word_len := (z x).nth 2
def z3 : bitvec word_len := (z x).nth 3
def z4 : bitvec word_len := (z x).nth 4
def z5 : bitvec word_len := (z x).nth 5
def z6 : bitvec word_len := (z x).nth 6
def z7 : bitvec word_len := (z x).nth 7
def z8 : bitvec word_len := (z x).nth 8
def z9 : bitvec word_len := (z x).nth 9
def z10 : bitvec word_len := (z x).nth 10
def z11 : bitvec word_len := (z x).nth 11
def z12 : bitvec word_len := (z x).nth 12
def z13 : bitvec word_len := (z x).nth 13
def z14 : bitvec word_len := (z x).nth 14
def z15 : bitvec word_len := (z x).nth 15

-- Salsa20(x) is the concatenation of 
-- littleendian⁻¹(z0 + x0),
-- littleendian⁻¹(z1 + x1),
-- littleendian⁻¹(z2 + x2),
-- ...
-- littleendian]⁻¹(z15 + x15).
def salsa20 : vector (bitvec byte_len) 64 := do
  let s0 := littleendian_inv ((z0 x) + (x0 x)),
  let s1 := littleendian_inv ((z1 x) + (x1 x)),
  let s2 := littleendian_inv ((z2 x) + (x2 x)),
  let s3 := littleendian_inv ((z3 x) + (x3 x)),
  let s4 := littleendian_inv ((z4 x) + (x4 x)),
  let s5 := littleendian_inv ((z5 x) + (x5 x)),
  let s6 := littleendian_inv ((z6 x) + (x6 x)),
  let s7 := littleendian_inv ((z7 x) + (x7 x)),
  let s8 := littleendian_inv ((z8 x) + (x8 x)),
  let s9 := littleendian_inv ((z9 x) + (x9 x)),
  let s10 := littleendian_inv ((z10 x) + (x10 x)),
  let s11 := littleendian_inv ((z11 x) + (x11 x)),
  let s12 := littleendian_inv ((z12 x) + (x12 x)),
  let s13 := littleendian_inv ((z13 x) + (x13 x)),
  let s14 := littleendian_inv ((z14 x) + (x14 x)),
  let s15 := littleendian_inv ((z15 x) + (x15 x)),

  (((((((((((((((s0.append s1).append s2).append s3)
    .append s4).append s5).append s6).append s7)
    .append s8).append s9).append s10)
    .append s11).append s12).append s13).append s14)
    .append s15)

lemma salsa20_zero : salsa20
  (list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ]) = list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ] :=
  begin
    -- not trivial with our current definitions
    sorry,
  end

lemma salsa_20_output_len_is_always_64 (x' : (vector (bitvec byte_len) 64)) : (salsa20.salsa20 x').length = 64 :=
begin
  refl,
end


namespace examples

#eval if salsa20
  (list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ]) = list.to_vec_of_bitvec byte_len 64 [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ] then tt else ff

#eval
  if salsa20 (list.to_vec_of_bitvec byte_len 64 [
    211, 159, 13, 115, 76, 55, 82, 183,
    3, 117, 222, 37, 191, 187, 234, 136,
    49, 237, 179, 48, 1, 106, 178, 219,
    175, 199, 166, 48, 86, 16, 179, 207,
    31, 240, 32, 63, 15, 83, 93, 161,
    116, 147, 48, 113, 238, 55, 204, 36,
    79, 201, 235, 79, 3, 81, 156, 47,
    203, 26, 244, 243, 88, 118, 104, 54
  ]) = list.to_vec_of_bitvec byte_len 64 [
    109, 42, 178, 168, 156, 240, 248, 238, 
    168, 196, 190, 203, 26, 110, 170, 154,
    29, 29, 150, 26, 150, 30, 235, 249, 
    190, 163, 251, 48, 69, 144, 51, 57,
    118, 40, 152, 157, 180, 57, 27, 94,
    107, 42, 236, 35, 27, 111, 114, 114,
    219, 236, 232, 135, 111, 155, 110, 18,
    24, 232, 95, 158, 179, 19, 48, 202
  ] then tt else ff

#eval
  if salsa20 (list.to_vec_of_bitvec byte_len 64 [
    88, 118, 104, 54, 79, 201, 235, 79,
    3, 81, 156, 47, 203, 26, 244, 243,
    191, 187, 234, 136, 211, 159, 13, 115,
    76, 55, 82, 183, 3, 117, 222, 37,
    86, 16, 179, 207, 49, 237, 179, 48,
    1, 106, 178, 219, 175, 199, 166, 48,
    238, 55,204, 36, 31, 240, 32, 63, 15,
    83, 93, 161, 116, 147, 48,113
  ]) = list.to_vec_of_bitvec byte_len 64 [
    179, 19, 48, 202, 219, 236, 232, 135,
    111, 155, 110, 18, 24, 232, 95, 158,
    26, 110, 170, 154, 109, 42, 178, 168,
    156, 240, 248, 238, 168, 196, 190, 203,
    69, 144, 51, 57, 29, 29, 150, 26,
    150, 30, 235, 249, 190, 163, 251, 48,
    27, 111, 114, 114, 118, 40, 152, 157,
    180, 57, 27, 94, 107, 42, 236, 35
  ] then tt else ff

end examples

end salsa20
