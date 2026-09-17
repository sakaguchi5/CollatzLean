import CollatzLean.Collatz3.Binary.Basic

/-!
# Collatz3 Binary: alternating binary weight

LSB 位置 `0` から見て、偶数位置と奇数位置の `1` の個数を別々に数える。
探索段階で使っていた `P2/P3` という仮称は導入しない。

primitive は二つの count と、その実現関係 `HasAlternatingWeight` だけ。
mod 3 や defect との関係は後段で導く。
-/

namespace Collatz3
namespace Binary

mutual
  /-- LSB-first 語の偶数位置 `0,2,4,...` にある `1` の個数。 -/
  def evenOneCount : List Bool → ℕ
    | [] => 0
    | b :: bs => bitValue b + oddOneCount bs

  /-- LSB-first 語の奇数位置 `1,3,5,...` にある `1` の個数。 -/
  def oddOneCount : List Bool → ℕ
    | [] => 0
    | _ :: bs => evenOneCount bs
end

@[simp] theorem evenOneCount_nil : evenOneCount [] = 0 := rfl
@[simp] theorem oddOneCount_nil : oddOneCount [] = 0 := rfl

@[simp] theorem evenOneCount_cons (b : Bool) (bs : List Bool) :
    evenOneCount (b :: bs) = bitValue b + oddOneCount bs := rfl

@[simp] theorem oddOneCount_cons (b : Bool) (bs : List Bool) :
    oddOneCount (b :: bs) = evenOneCount bs := rfl

/--
自然数 `x` が長さ `length` の二進語で表され、その alternating weight が
`evenWeight, oddWeight` である。

bit length の canonicality は別 predicate `HasBitLength` に分離する。
-/
def HasAlternatingWeight
    (x evenWeight oddWeight length : ℕ) : Prop :=
  ∃ bits : List Bool,
    RepresentsAtLength bits x length ∧
      evenOneCount bits = evenWeight ∧
      oddOneCount bits = oddWeight

namespace HasAlternatingWeight

/-- 具体的な固定長 binary representation から alternating weight を得る。 -/
theorem of_representation
    {bits : List Bool} {x length : ℕ}
    (h : RepresentsAtLength bits x length) :
    HasAlternatingWeight
      x (evenOneCount bits) (oddOneCount bits) length := by
  exact ⟨bits, h, rfl, rfl⟩

/-- alternating weight には固定長 representation が付随する。 -/
theorem exists_representation
    {x evenWeight oddWeight length : ℕ}
    (h : HasAlternatingWeight x evenWeight oddWeight length) :
    ∃ bits : List Bool,
      RepresentsAtLength bits x length := by
  rcases h with ⟨bits, hRep, hEven, hOdd⟩
  exact ⟨bits, hRep⟩

end HasAlternatingWeight

end Binary
end Collatz3
