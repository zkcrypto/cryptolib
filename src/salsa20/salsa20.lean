/-
  Section 8 : The Salsa20 hash function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.words
import salsa20.doubleround
import salsa20.littleendian

namespace salsa20

-- x is a 64-byte sequence
-- TODO: try vector instead of list to limit the length (everywhere) 
variable x : list (bitvec byte_len)

-- x0 = littleendian(x[0], x[1], x[2], x[3])
def x0 : bitvec word_len := littleendian 
  (x.nth 0).iget 
  (x.nth 1).iget
  (x.nth 2).iget
  (x.nth 3).iget

-- x1 = littleendian(x[4], x[5], x[6], x[7])
def x1 : bitvec word_len := littleendian 
  (x.nth 4).iget 
  (x.nth 5).iget 
  (x.nth 6).iget 
  (x.nth 7).iget

-- x2 = littleendian(x[8], x[9], x[10], x[11])
def x2 : bitvec word_len := littleendian 
  (x.nth 8).iget 
  (x.nth 9).iget 
  (x.nth 10).iget 
  (x.nth 11).iget

-- x3 = littleendian(x[12], x[13], x[14], x[15])
def x3 : bitvec word_len := littleendian 
  (x.nth 12).iget 
  (x.nth 13).iget 
  (x.nth 14).iget 
  (x.nth 15).iget

-- x4 = littleendian(x[16], x[17], x[18], x[19])
def x4 : bitvec word_len := littleendian 
  (x.nth 16).iget 
  (x.nth 17).iget 
  (x.nth 18).iget 
  (x.nth 19).iget

-- x5 = littleendian(x[20], x[21], x[22], x[23])
def x5 : bitvec word_len := littleendian 
  (x.nth 20).iget 
  (x.nth 21).iget 
  (x.nth 22).iget 
  (x.nth 23).iget

-- x6 = littleendian(x[24], x[25], x[26], x[27])
def x6 : bitvec word_len := littleendian 
  (x.nth 24).iget 
  (x.nth 25).iget 
  (x.nth 26).iget 
  (x.nth 27).iget

-- x7 = littleendian(x[28], x[29], x[30], x[31])
def x7 : bitvec word_len := littleendian 
  (x.nth 28).iget 
  (x.nth 29).iget 
  (x.nth 30).iget 
  (x.nth 31).iget

-- x8 = littleendian(x[32], x[33], x[34], x[35])
def x8 : bitvec word_len := littleendian 
  (x.nth 32).iget 
  (x.nth 33).iget 
  (x.nth 34).iget 
  (x.nth 35).iget

-- x9 = littleendian(x[36], x[37], x[38], x[39])
def x9 : bitvec word_len := littleendian 
  (x.nth 36).iget 
  (x.nth 37).iget 
  (x.nth 38).iget 
  (x.nth 39).iget

-- x10 = littleendian(x[40], x[41], x[42], x[43])
def x10 : bitvec word_len := littleendian 
  (x.nth 40).iget 
  (x.nth 41).iget 
  (x.nth 42).iget 
  (x.nth 43).iget

-- x11 = littleendian(x[44], x[45], x[46], x[47])
def x11 : bitvec word_len := littleendian 
  (x.nth 44).iget 
  (x.nth 45).iget 
  (x.nth 46).iget 
  (x.nth 47).iget

-- x12 = littleendian(x[48], x[49], x[50], x[51])
def x12 : bitvec word_len := littleendian 
  (x.nth 48).iget 
  (x.nth 49).iget 
  (x.nth 50).iget 
  (x.nth 51).iget

-- x13 = littleendian(x[52], x[53], x[54], x[55])
def x13 : bitvec word_len := littleendian 
  (x.nth 52).iget 
  (x.nth 53).iget 
  (x.nth 54).iget 
  (x.nth 55).iget

-- x14 = littleendian(x[56], x[57], x[58], x[59])
def x14 : bitvec word_len := littleendian 
  (x.nth 56).iget 
  (x.nth 57).iget 
  (x.nth 58).iget 
  (x.nth 59).iget

-- x15 = littleendian(x[60], x[61], x[62], x[63])
def x15 : bitvec word_len := littleendian 
  (x.nth 60).iget 
  (x.nth 61).iget 
  (x.nth 62).iget 
  (x.nth 63).iget

-- Doubleround to the n power (doubleround n times)
def doubleround_exp_n : ℕ → list (bitvec word_len) → list (bitvec word_len)
| 0 l := l
| (n+1) l := do {
    let w0 := (l.nth 0).iget,
    let w1 := (l.nth 1).iget,
    let w2 := (l.nth 2).iget,
    let w3 := (l.nth 3).iget,
    let w4 := (l.nth 4).iget,
    let w5 := (l.nth 5).iget,
    let w6 := (l.nth 6).iget,
    let w7 := (l.nth 7).iget,
    let w8 := (l.nth 8).iget,
    let w9 := (l.nth 9).iget,
    let w10 := (l.nth 10).iget,
    let w11 := (l.nth 11).iget,
    let w12 := (l.nth 12).iget,
    let w13 := (l.nth 13).iget,
    let w14 := (l.nth 14).iget,
    let w15 := (l.nth 15).iget,

    let round := doubleround w0 w1 w2 w3 w4 w5 w6 w7 w8
      w9 w10 w11 w12 w13 w14 w15,

    doubleround_exp_n (n) round
}

-- (z0, z1, . . . , z15) = doubleround¹⁰(x0, x1, . . . , x15)
def z : list (bitvec word_len) := 
  doubleround_exp_n 10 [
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
  ]
  
def z0 : bitvec word_len := (list.nth (z x) 0).iget
def z1 : bitvec word_len := (list.nth (z x) 1).iget
def z2 : bitvec word_len := (list.nth (z x) 2).iget
def z3 : bitvec word_len := (list.nth (z x) 3).iget
def z4 : bitvec word_len := (list.nth (z x) 4).iget
def z5 : bitvec word_len := (list.nth (z x) 5).iget
def z6 : bitvec word_len := (list.nth (z x) 6).iget
def z7 : bitvec word_len := (list.nth (z x) 7).iget
def z8 : bitvec word_len := (list.nth (z x) 8).iget
def z9 : bitvec word_len := (list.nth (z x) 9).iget
def z10 : bitvec word_len := (list.nth (z x) 10).iget
def z11 : bitvec word_len := (list.nth (z x) 11).iget
def z12 : bitvec word_len := (list.nth (z x) 12).iget
def z13 : bitvec word_len := (list.nth (z x) 13).iget
def z14 : bitvec word_len := (list.nth (z x) 14).iget
def z15 : bitvec word_len := (list.nth (z x) 15).iget

-- Salsa20(x) is the concatenation of 
-- littleendian⁻¹(z0 + x0),
-- littleendian⁻¹(z1 + x1),
-- littleendian⁻¹(z2 + x2),
-- ...
-- littleendian]⁻¹(z15 + x15).
def salsa20 : list (bitvec byte_len) := do
  let s0 := littleendian_inv (bitvec.of_nat word_len ((z0 x).to_nat + (x0 x).to_nat)),
  let s1 := littleendian_inv (bitvec.of_nat word_len ((z1 x).to_nat + (x1 x).to_nat)),
  let s2 := littleendian_inv (bitvec.of_nat word_len ((z2 x).to_nat + (x2 x).to_nat)),
  let s3 := littleendian_inv (bitvec.of_nat word_len ((z3 x).to_nat + (x3 x).to_nat)),
  let s4 := littleendian_inv (bitvec.of_nat word_len ((z4 x).to_nat + (x4 x).to_nat)),
  let s5 := littleendian_inv (bitvec.of_nat word_len ((z5 x).to_nat + (x5 x).to_nat)),
  let s6 := littleendian_inv (bitvec.of_nat word_len ((z6 x).to_nat + (x6 x).to_nat)),
  let s7 := littleendian_inv (bitvec.of_nat word_len ((z7 x).to_nat + (x7 x).to_nat)),
  let s8 := littleendian_inv (bitvec.of_nat word_len ((z8 x).to_nat + (x8 x).to_nat)),
  let s9 := littleendian_inv (bitvec.of_nat word_len ((z9 x).to_nat + (x9 x).to_nat)),
  let s10 := littleendian_inv (bitvec.of_nat word_len ((z10 x).to_nat + (x10 x).to_nat)),
  let s11 := littleendian_inv (bitvec.of_nat word_len ((z11 x).to_nat + (x11 x).to_nat)),
  let s12 := littleendian_inv (bitvec.of_nat word_len ((z12 x).to_nat + (x12 x).to_nat)),
  let s13 := littleendian_inv (bitvec.of_nat word_len ((z13 x).to_nat + (x13 x).to_nat)),
  let s14 := littleendian_inv (bitvec.of_nat word_len ((z14 x).to_nat + (x14 x).to_nat)),
  let s15 := littleendian_inv (bitvec.of_nat word_len((z15 x).to_nat + (x15 x).to_nat)),

  (((((((((((((((s0.append s1).append s2).append s3)
    .append s4).append s5).append s6).append s7)
    .append s8).append s9).append s10)
    .append s11).append s12).append s13).append s14)
    .append s15)


lemma salsa20_zero : salsa20
  [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ] = [
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
    -- not trivial with out current definitions
    sorry,
  end

lemma salsa_20_output_len_is_always_64 (x' : list (bitvec byte_len)) : (salsa20.salsa20 x').length = 64 :=
begin
  refl,
end


namespace examples

#eval if salsa20
  [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0
  ] = [
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
  if salsa20 [
    211, 159, 13, 115, 76, 55, 82, 183,
    3, 117, 222, 37, 191, 187, 234, 136,
    49, 237, 179, 48, 1, 106, 178, 219,
    175, 199, 166, 48, 86, 16, 179, 207,
    31, 240, 32, 63, 15, 83, 93, 161,
    116, 147, 48, 113, 238, 55, 204, 36,
    79, 201, 235, 79, 3, 81, 156, 47,
    203, 26, 244, 243, 88, 118, 104, 54
  ] = [
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
  if salsa20 [
    88, 118, 104, 54, 79, 201, 235, 79,
    3, 81, 156, 47, 203, 26, 244, 243,
    191, 187, 234, 136, 211, 159, 13, 115,
    76, 55, 82, 183, 3, 117, 222, 37,
    86, 16, 179, 207, 49, 237, 179, 48,
    1, 106, 178, 219, 175, 199, 166, 48,
    238, 55,204, 36, 31, 240, 32, 63, 15,
    83, 93, 161, 116, 147, 48,113
  ] = [
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
