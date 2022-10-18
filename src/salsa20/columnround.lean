/-
  Section 5 : The columnrow function
  http://cr.yp.to/snuffle/spec.pdf
-/
import salsa20.quarterround

-- (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
def columnround1 (x₀ x₄ x₈ x₁₂ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₀, x₄, x₈, x₁₂].to_vec_of_bitvec word_len 4)

-- (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
def columnround2 (x₅ x₉ x₁₃ x₁ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₅, x₉, x₁₃, x₁].to_vec_of_bitvec word_len 4)

-- (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
def columnround3 (x₁₀ x₁₄ x₂ x₆ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₁₀, x₁₄, x₂, x₆].to_vec_of_bitvec word_len 4)

-- (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
def columnround4 (x₁₅ x₃ x₇ x₁₁ : bitvec word_len) : vector (bitvec word_len) 4 := 
  quarterround ([x₁₅, x₃, x₇, x₁₁].to_vec_of_bitvec word_len 4)

-- If x = (x₀, x₁, x₂, x₃, ... , x₁₅) then 
-- columnround(x) = (y₀, y₁, y₂, y₃, ... , y₁₅) where
-- (y₀, y₄, y₈, y₁₂) = quarterround(x₀, x₄, x₈, x₁₂)
-- (y₅, y₉, y₁₃, y₁) = quarterround(x₅, x₉, x₁₃, x₁)
-- (y₁₀, y₁₄, y₂, y₆) = quarterround(x₁₀, x₁₄, x₂, x₆)
-- (y₁₅, y₃, y₇, y₁₁) = quarterround(x₁₅, x₃, x₇, x₁₁)
def columnround
  (x : vector (bitvec word_len) 16) : vector (bitvec word_len) 16 :=
  do
    let list1 := columnround1 (x.nth 0) (x.nth 4) (x.nth 8) (x.nth 12),
    let list2 := columnround2 (x.nth 5) (x.nth 9) (x.nth 13) (x.nth 1),
    let list3 := columnround3 (x.nth 10) (x.nth 14) (x.nth 2) (x.nth 6),
    let list4 := columnround4 (x.nth 15) (x.nth 3) (x.nth 7) (x.nth 11),

    let y₀ := list1.head,
    let y₄ := list1.nth 1,
    let y₈ := list1.nth 2,
    let y₁₂ := list1.nth 3,

    let y₅ := list2.head,
    let y₉ := list2.nth 1,
    let y₁₃ := list2.nth 2,
    let y₁ := list2.nth 3,

    let y₁₀ := list3.head,
    let y₁₄ := list3.nth 1,
    let y₂ := list3.nth 2,
    let y₆ := list3.nth 3,

    let y₁₅ := list4.head,
    let y₃ := list4.nth 1,
    let y₇ := list4.nth 2,
    let y₁₁ := list4.nth 3,

    [y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂, y₁₃, y₁₄, y₁₅].to_vec_of_bitvec word_len 16

lemma columnround_zero : 
  columnround ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].to_vec_of_bitvec word_len 16) = 
    [0, 0, 0 ,0, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0, 0, 0].to_vec_of_bitvec word_len 16 := rfl

-- example 1
namespace example5_1

def x₀ : bitvec word_len := 0x00000001
def x₁ : bitvec word_len := 0x00000000
def x₂ : bitvec word_len := 0x00000000
def x₃ : bitvec word_len := 0x00000000
def x₄ : bitvec word_len := 0x00000001
def x₅ : bitvec word_len := 0x00000000
def x₆ : bitvec word_len := 0x00000000
def x₇ : bitvec word_len := 0x00000000
def x₈ : bitvec word_len := 0x00000001
def x₉ : bitvec word_len := 0x00000000
def x₁₀ : bitvec word_len := 0x00000000
def x₁₁ : bitvec word_len := 0x00000000
def x₁₂ : bitvec word_len := 0x00000001
def x₁₃ : bitvec word_len := 0x00000000
def x₁₄ : bitvec word_len := 0x00000000
def x₁₅ : bitvec word_len := 0x00000000

def x : vector (bitvec word_len) 16 := 
  [x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀, x₁₁, x₁₂, x₁₃, x₁₄, x₁₅].to_vec_of_bitvec word_len 16

-- y₀
#eval ((columnround x).nth 0).to_nat
#eval 0x10090288

-- y₁
#eval ((columnround x).nth 1).to_nat
#eval 0x00000000

-- y₂
#eval ((columnround x).nth 2).to_nat
#eval 0x00000000

-- y₃
#eval ((columnround x).nth 3).to_nat
#eval 0x00000000

-- y₄
#eval ((columnround x).nth 4).to_nat
#eval 0x00000101

-- y₅
#eval ((columnround x).nth 5).to_nat
#eval 0x00000000

-- y₆
#eval ((columnround x).nth 6).to_nat
#eval 0x00000000

-- y₇
#eval ((columnround x).nth 7).to_nat
#eval 0x00000000

-- y₈
#eval ((columnround x).nth 8).to_nat
#eval 0x00020401

-- y₉
#eval ((columnround x).nth 9).to_nat
#eval 0x00000000

-- y₁₀
#eval ((columnround x).nth 10).to_nat
#eval 0x00000000

-- y₁₁
#eval ((columnround x).nth 11).to_nat
#eval 0x00000000

-- y₁₂
#eval ((columnround x).nth 12).to_nat
#eval 0x40a04001

-- y₁₃
#eval ((columnround x).nth 13).to_nat
#eval 0x00000000

-- y₁₄
#eval ((columnround x).nth 14).to_nat
#eval 0x00000000

-- y₁₅
#eval ((columnround x).nth 15).to_nat
#eval 0x00000000

end example5_1

-- example 2
namespace example5_2

def x₀ : bitvec word_len := 0x08521bd6
def x₁ : bitvec word_len := 0x1fe88837
def x₂ : bitvec word_len := 0xbb2aa576
def x₃ : bitvec word_len := 0x3aa26365
def x₄ : bitvec word_len := 0xc54c6a5b
def x₅ : bitvec word_len := 0x2fc74c2f
def x₆ : bitvec word_len := 0x6dd39cc3
def x₇ : bitvec word_len := 0xda0a64f6
def x₈ : bitvec word_len := 0x90a2f23d
def x₉ : bitvec word_len := 0x067f95a6
def x₁₀ : bitvec word_len := 0x06b35f61
def x₁₁ : bitvec word_len := 0x41e4732e
def x₁₂ : bitvec word_len := 0xe859c100
def x₁₃ : bitvec word_len := 0xea4d84b7
def x₁₄ : bitvec word_len := 0x0f619bff
def x₁₅ : bitvec word_len := 0xbc6e965a

def x : vector (bitvec word_len) 16 := 
  [x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀, x₁₁, x₁₂, x₁₃, x₁₄, x₁₅].to_vec_of_bitvec word_len 16

-- y₀
#eval ((columnround x).nth 0).to_nat
#eval 0x8c9d190a

-- y₁
#eval ((columnround x).nth 1).to_nat
#eval 0xce8e4c90

-- y₂
#eval ((columnround x).nth 2).to_nat
#eval 0x1ef8e9d3

-- y₃
#eval ((columnround x).nth 3).to_nat
#eval 0x1326a71a

-- y₄
#eval ((columnround x).nth 4).to_nat
#eval 0x90a20123

-- y₅
#eval ((columnround x).nth 5).to_nat
#eval 0xead3c4f3

-- y₆
#eval ((columnround x).nth 6).to_nat
#eval 0x63a091a0

-- y₇
#eval ((columnround x).nth 7).to_nat
#eval 0xf0708d69

-- y₈
#eval ((columnround x).nth 8).to_nat
#eval 0x789b010c

-- y₉
#eval ((columnround x).nth 9).to_nat
#eval 0xd195a681

-- y₁₀
#eval ((columnround x).nth 10).to_nat
#eval 0xeb7d5504

-- y₁₁
#eval ((columnround x).nth 11).to_nat
#eval 0xa774135c

-- y₁₂
#eval ((columnround x).nth 12).to_nat
#eval 0x481c2027

-- y₁₃
#eval ((columnround x).nth 13).to_nat
#eval 0x53a8e4b5

-- y₁₄
#eval ((columnround x).nth 14).to_nat
#eval 0x4c1f89c5

-- y₁₅
#eval ((columnround x).nth 15).to_nat
#eval 0x3f78c9c8

end example5_2

-- TODO: equivalent formula
-- TODO: matrix form
