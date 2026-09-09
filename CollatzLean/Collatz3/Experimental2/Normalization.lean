import CollatzLean.Collatz3.Experimental2.CarryCore

/-!
# Collatz3 Experimental2: 屋根の正規化

`normalizeRoof β n = β(n) - n*β(1)` と置き、
整数線形成分だけを取り除く。

重要なのは、正規化が

* unit-carry 性を保存する
* carry 自体を完全に保存する
* 二度正規化しても変わらない

という射影になっていることである。
-/

namespace Collatz3
namespace Experimental2

/-- `β(1)` による整数線形成分を取り除いた正規化屋根。 -/
def normalizeRoof
    (β : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  β n - n * β 1

namespace HasUnitCarry

/-- 線形成分 `n*β(1)` は常に `β(n)` 以下。 -/
theorem linearPart_le
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    n * β 1 ≤ β n := by
  simpa using U.mul_lower n 1

/-- 元の屋根は「整数線形成分 + 正規化屋根」に exact 分解できる。 -/
theorem eq_linear_add_normalizeRoof
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    β n = n * β 1 + normalizeRoof β n := by
  have hLe := U.linearPart_le n
  unfold normalizeRoof
  omega

/-- 正規化屋根の `1` での値は `0`。 -/
@[simp] theorem normalizeRoof_one
    {β : ℕ → ℕ} :
    normalizeRoof β 1 = 0 := by
  simp [normalizeRoof]

/-- 正規化屋根の原点は `0`。 -/
@[simp] theorem normalizeRoof_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    normalizeRoof β 0 = 0 := by
  simp [normalizeRoof, U.zero_eq]

/-- 正規化屋根の加法 law。carry は元の屋根と同じ。 -/
theorem normalizeRoof_add_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    normalizeRoof β (a + b) =
      normalizeRoof β a + normalizeRoof β b +
        roofCarry β a b := by
  have hA := U.eq_linear_add_normalizeRoof a
  have hB := U.eq_linear_add_normalizeRoof b
  have hAB := U.eq_linear_add_normalizeRoof (a + b)
  have hAdd := U.add_eq a b
  simp only [Nat.add_mul] at hAB
  omega

/-- 正規化屋根も unit-carry。 -/
theorem normalizeRoof_hasUnitCarry
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    HasUnitCarry (normalizeRoof β) := by
  unfold HasUnitCarry
  constructor
  · unfold IsSuperadditiveRoof
    intro a b
    have hAdd := U.normalizeRoof_add_eq a b
    omega
  · unfold HasUnitUpperDefect
    intro a b
    have hAdd := U.normalizeRoof_add_eq a b
    have hCarryLe := U.carry_le_one a b
    omega

/-- 正規化しても carry は完全に保存される。 -/
theorem roofCarry_normalizeRoof_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry (normalizeRoof β) a b = roofCarry β a b := by
  have hAdd := U.normalizeRoof_add_eq a b
  unfold roofCarry at hAdd ⊢
  omega

end HasUnitCarry

/-- 正規化は冪等。 -/
theorem normalizeRoof_idempotent
    {β : ℕ → ℕ}
    (n : ℕ) :
    normalizeRoof (normalizeRoof β) n = normalizeRoof β n := by
  simp [normalizeRoof]

end Experimental2
end Collatz3
