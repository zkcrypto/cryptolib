/-
  Section 4 : The rowround function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.quarterround

-- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
def rowround1 (y₀ y₁ y₂ y₃ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₀, y₁, y₂, y₃].to_vec_of_bitvec word_len 4)

-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
def rowround2 (y₅ y₆ y₇ y₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₅, y₆, y₇, y₄].to_vec_of_bitvec word_len 4)

-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
def rowround3 (y₁₀ y₁₁ y₈ y₉ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₁₀, y₁₁, y₈, y₉].to_vec_of_bitvec word_len 4)

-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround4 (y₁₅ y₁₂ y₁₃ y₁₄ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([y₁₅, y₁₂, y₁₃, y₁₄].to_vec_of_bitvec word_len 4)

-- If y = (y₀, y₁, y₂, y₃, ... , y₁₅) then 
-- rowround(y) = (z₀, z₁, z₂, z₃, ... , z₁₅) where
-- (z₀, z₁, z₂, z₃) = quarterround(y₀, y₁, y₂, y₃)
-- (z₅, z₆, z₇, z₄) = quarterround(y₅, y₆, y₇, y₄)
-- (z₁₀, z₁₁, z₈, z₉) = quarterround(y₁₀, y₁₁, y₈, y₉)
-- (z₁₅, z₁₂, z₁₃, z₁₄) = quarterround(y₁₅, y₁₂, y₁₃, y₁₄)
def rowround (y : vector(bitvec word_len) 16) : vector (bitvec word_len) 16 :=
  do
    let list1 := rowround1 (y.nth 0) (y.nth 1) (y.nth 2) (y.nth 3),
    let list2 := rowround2 (y.nth 5) (y.nth 6) (y.nth 7) (y.nth 4),
    let list3 := rowround3 (y.nth 10) (y.nth 11) (y.nth 8) (y.nth 9),
    let list4 := rowround4 (y.nth 15) (y.nth 12) (y.nth 13) (y.nth 14),

    let z₅ := list2.head,
    let z₆ := list2.nth 1,
    let z₇ := list2.nth 2,
    let z₄ := list2.nth 3,

    let list2_sorted := [z₄, z₅, z₆, z₇].to_vec_of_bitvec word_len 4, 

    let z₁₀ := list3.head,
    let z₁₁ := list3.nth 1,
    let z₈ := list3.nth 2,
    let z₉ := list3.nth 3,

    let list3_sorted := [z₈, z₉, z₁₀, z₁₁].to_vec_of_bitvec word_len 4,

    let z₁₅ := list4.head,
    let z₁₂ := list4.nth 1,
    let z₁₃ := list4.nth 2,
    let z₁₄ := list4.nth 3,

    let list4_sorted := [z₁₂, z₁₃, z₁₄, z₁₅].to_vec_of_bitvec word_len 4,
    
    ((list1.append list2_sorted).append list3_sorted).append list4_sorted

lemma rowround_zero : 
  rowround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

-- example 1
namespace example4_1

def y₀ : bitvec word_len := 0x00000001
def y₁ : bitvec word_len := 0x00000000
def y₂ : bitvec word_len := 0x00000000
def y₃ : bitvec word_len := 0x00000000
def y₄ : bitvec word_len := 0x00000001
def y₅ : bitvec word_len := 0x00000000
def y₆ : bitvec word_len := 0x00000000
def y₇  : bitvec word_len := 0x00000000
def y₈ : bitvec word_len := 0x00000001
def y₉ : bitvec word_len := 0x00000000
def y₁₀ : bitvec word_len := 0x00000000
def y₁₁ : bitvec word_len := 0x00000000
def y₁₂ : bitvec word_len := 0x00000001
def y₁₃ : bitvec word_len := 0x00000000
def y₁₄ : bitvec word_len := 0x00000000
def y₁₅ : bitvec word_len := 0x00000000

def y : vector (bitvec word_len) 16 := 
  [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16

-- z₀
#eval ((rowround y).nth 0).to_nat
#eval 0x08008145

-- z₁
#eval ((rowround y).nth 1).to_nat
#eval 0x00000080

-- z₂
#eval ((rowround y).nth 2).to_nat
#eval 0x00010200

-- z₃
#eval ((rowround y).nth 3).to_nat
#eval 0x20500000

-- z₄
#eval ((rowround y).nth 4).to_nat
#eval 0x20100001

-- z₅
#eval ((rowround y).nth 5).to_nat
#eval 0x00048044

-- z₆
#eval ((rowround y).nth 6).to_nat
#eval 0x00000080

-- z₇
#eval ((rowround y).nth 7).to_nat
#eval 0x00010000

-- z₈
#eval ((rowround y).nth 8).to_nat
#eval 0x00000001

-- z₉
#eval ((rowround y).nth 9).to_nat
#eval 0x00002000

-- z₁₀
#eval ((rowround y).nth 10).to_nat
#eval 0x80040000

-- z₁₁
#eval ((rowround y).nth 11).to_nat
#eval 0x00000000

-- z₁₂
#eval ((rowround y).nth 12).to_nat
#eval 0x00000001

-- z₁₃
#eval ((rowround y).nth 13).to_nat
#eval 0x00000200

-- z₁₄
#eval ((rowround y).nth 14).to_nat
#eval 0x00402000

-- z₁₅
#eval ((rowround y).nth 15).to_nat
#eval 0x88000100

end example4_1

-- example 2
namespace example4_2

def y₀ : bitvec word_len := 0x08521bd6
def y₁ : bitvec word_len := 0x1fe88837
def y₂ : bitvec word_len := 0xbb2aa576
def y₃ : bitvec word_len := 0x3aa26365
def y₄ : bitvec word_len := 0xc54c6a5b
def y₅ : bitvec word_len := 0x2fc74c2f
def y₆ : bitvec word_len := 0x6dd39cc3
def y₇ : bitvec word_len := 0xda0a64f6
def y₈ : bitvec word_len := 0x90a2f23d
def y₉ : bitvec word_len := 0x067f95a6
def y₁₀ : bitvec word_len := 0x06b35f61
def y₁₁ : bitvec word_len := 0x41e4732e
def y₁₂ : bitvec word_len := 0xe859c100
def y₁₃ : bitvec word_len := 0xea4d84b7
def y₁₄ : bitvec word_len := 0x0f619bff
def y₁₅ : bitvec word_len := 0xbc6e965a

def y : vector (bitvec word_len) 16 := 
  [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16

-- z₀
#eval ((rowround y).nth 0).to_nat
#eval 0xa890d39d

-- z₁
#eval ((rowround y).nth 1).to_nat
#eval 0x65d71596

-- z₂
#eval ((rowround y).nth 2).to_nat
#eval 0xe9487daa

-- z₃
#eval ((rowround y).nth 3).to_nat
#eval 0xc8ca6a86

-- z₄
#eval ((rowround y).nth 4).to_nat
#eval 0x949d2192

-- z₅
#eval ((rowround y).nth 5).to_nat
#eval 0x764b7754

-- z₆
#eval ((rowround y).nth 6).to_nat
#eval 0xe408d9b9

-- z₇
#eval ((rowround y).nth 7).to_nat
#eval 0x7a41b4d1

-- z₈
#eval ((rowround y).nth 8).to_nat
#eval 0x3402e183

-- z₉
#eval ((rowround y).nth 9).to_nat
#eval 0x3c3af432

-- z₁₀
#eval ((rowround y).nth 10).to_nat
#eval 0x50669f96

-- z₁₁
#eval ((rowround y).nth 11).to_nat
#eval 0xd89ef0a8

-- z₁₂
#eval ((rowround y).nth 12).to_nat
#eval 0x0040ede5

-- z₁₃
#eval ((rowround y).nth 13).to_nat
#eval 0xb545fbce

-- z₁₄
#eval ((rowround y).nth 14).to_nat
#eval 0xd257ed4f

-- z₁₅
#eval ((rowround y).nth 15).to_nat
#eval 0x1818882d

end example4_2

-- TODO: matrix form
