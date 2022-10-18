/-
  Section 6 : The doubleround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.rowround
import salsa20.columnround

-- A double round is a column round followed by a row round: doubleround(x) =
-- rowround(columnround(x))
def doubleround(x : vector (bitvec word_len) 16) : vector (bitvec word_len) 16 := do
  let cr := columnround x,
  let y₀ := cr.nth 0,
  let y₁ := cr.nth 1,
  let y₂ := cr.nth 2,
  let y₃ := cr.nth 3,
  let y₄ := cr.nth 4,
  let y₅ := cr.nth 5,
  let y₆ := cr.nth 6,
  let y₇ := cr.nth 7,
  let y₈ := cr.nth 8,
  let y₉ := cr.nth 9,
  let y₁₀ := cr.nth 10,
  let y₁₁ := cr.nth 11,
  let y₁₂ := cr.nth 12,
  let y₁₃ := cr.nth 13,
  let y₁₄ := cr.nth 14,
  let y₁₅ := cr.nth 15,

  rowround ([y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16)

lemma doubleround_zero : 
  doubleround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl


-- example 1
namespace example6_1

def x₀ : bitvec word_len := 0x00000001
def x₁ : bitvec word_len := 0x00000000
def x₂ : bitvec word_len := 0x00000000
def x₃ : bitvec word_len := 0x00000000
def x₄ : bitvec word_len := 0x00000000
def x₅ : bitvec word_len := 0x00000000
def x₆ : bitvec word_len := 0x00000000
def x₇ : bitvec word_len := 0x00000000
def x₈ : bitvec word_len := 0x00000000
def x₉ : bitvec word_len := 0x00000000
def x₁₀ : bitvec word_len := 0x00000000
def x₁₁ : bitvec word_len := 0x00000000
def x₁₂ : bitvec word_len := 0x00000000
def x₁₃ : bitvec word_len := 0x00000000
def x₁₄ : bitvec word_len := 0x00000000
def x₁₅ : bitvec word_len := 0x00000000

def x : vector (bitvec word_len) 16 := 
  [x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀, x₁₁, x₁₂, x₁₃, x₁₄, x₁₅].to_vec_of_bitvec word_len 16

-- double₀
#eval ((doubleround x).nth 0).to_nat
#eval 0x8186a22d

-- double₁
#eval ((doubleround x).nth 1).to_nat
#eval 0x0040a284

--  double₂
#eval ((doubleround x).nth 2).to_nat
#eval 0x82479210

-- double₃
#eval ((doubleround x).nth 3).to_nat
#eval 0x06929051

-- double₄
#eval ((doubleround x).nth 4).to_nat
#eval 0x08000090

-- double₅
#eval ((doubleround x).nth 5).to_nat
#eval 0x02402200

-- double₆
#eval ((doubleround x).nth 6).to_nat
#eval 0x00004000

-- double₇
#eval ((doubleround x).nth 7).to_nat
#eval 0x00800000

-- double₈
#eval ((doubleround x).nth 8).to_nat
#eval 0x00010200

-- double₉
#eval ((doubleround x).nth 9).to_nat
#eval 0x20400000

-- double₁₀
#eval ((doubleround x).nth 10).to_nat
#eval 0x08008104

-- double₁₁
#eval ((doubleround x).nth 11).to_nat
#eval 0x00000000

-- double₁₂
#eval ((doubleround x).nth 12).to_nat
#eval 0x20500000

-- double₁₃
#eval ((doubleround x).nth 13).to_nat
#eval 0xa0000040

-- double₁₄
#eval ((doubleround x).nth 14).to_nat
#eval 0x0008180a

-- double₁₅
#eval ((doubleround x).nth 15).to_nat
#eval 0x612a8020

end example6_1

-- example 2
namespace example6_2

def x₀ : bitvec word_len := 0xde501066
def x₁ : bitvec word_len := 0x6f9eb8f7
def x₂ : bitvec word_len := 0xe4fbbd9b
def x₃ : bitvec word_len := 0x454e3f57
def x₄ : bitvec word_len := 0xb75540d3
def x₅ : bitvec word_len := 0x43e93a4c
def x₆ : bitvec word_len := 0x3a6f2aa0
def x₇ : bitvec word_len := 0x726d6b36
def x₈ : bitvec word_len := 0x9243f484
def x₉ : bitvec word_len := 0x9145d1e8
def x₁₀ : bitvec word_len := 0x4fa9d247
def x₁₁ : bitvec word_len := 0xdc8dee11
def x₁₂ : bitvec word_len := 0x054bf545
def x₁₃ : bitvec word_len := 0x254dd653
def x₁₄ : bitvec word_len := 0xd9421b6d
def x₁₅ : bitvec word_len := 0x67b276c1

def x : vector (bitvec word_len) 16 := 
  [x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀, x₁₁, x₁₂, x₁₃, x₁₄, x₁₅].to_vec_of_bitvec word_len 16

-- double₀
#eval ((doubleround x).nth 0).to_nat
#eval 0xccaaf672

-- double₁
#eval ((doubleround x).nth 1).to_nat
#eval 0x23d960f7

-- double₂
#eval ((doubleround x).nth 2).to_nat
#eval 0x9153e63a

-- double₃
#eval ((doubleround x).nth 3).to_nat
#eval 0xcd9a60d0

-- double₄
#eval ((doubleround x).nth 4).to_nat
#eval 0x50440492

-- double₅
#eval ((doubleround x).nth 5).to_nat
#eval 0xf07cad19

-- double₆
#eval ((doubleround x).nth 6).to_nat
#eval 0xae344aa0

-- double₇
#eval ((doubleround x).nth 7).to_nat
#eval 0xdf4cfdfc

-- double₈
#eval ((doubleround x).nth 8).to_nat
#eval 0xca531c29

--  double₉
#eval ((doubleround x).nth 9).to_nat
#eval 0x8e7943db

-- double₁₀
#eval ((doubleround x).nth 10).to_nat
#eval 0xac1680cd

-- double₁₁
#eval ((doubleround x).nth 11).to_nat
#eval 0xd503ca00

-- double₁₂
#eval ((doubleround x).nth 12).to_nat
#eval 0xa74b2ad6

-- double₁₃
#eval ((doubleround x).nth 13).to_nat
#eval 0xbc331c5c

-- double₁₄
#eval ((doubleround x).nth 14).to_nat
#eval 0x1dda24c7

-- double₁₅
#eval ((doubleround x).nth 15).to_nat
#eval 0xee928277

end example6_2
