import CollatzLean.Collatz3.Experimental2.RoofCore

/-!
# Collatz3 Experimental2: carry の基本算術

carry は primitive field ではなく、屋根から計算する差分として定義する。

下側超加法性により Nat subtraction が lossless になり、
上側一単位誤差を加えると carry は exact に `0` または `1` になる。
-/

namespace Collatz3
namespace Experimental2

/-- 屋根の二項 carry。 -/
def roofCarry (β : ℕ → ℕ) (a b : ℕ) : ℕ :=
  β (a + b) - (β a + β b)

namespace IsSuperadditiveRoof

/-- 超加法性の下での exact addition formula。 -/
theorem add_eq
    {β : ℕ → ℕ}
    (L : IsSuperadditiveRoof β)
    (a b : ℕ) :
    β (a + b) = β a + β b + roofCarry β a b := by
  have hLower := L a b
  unfold roofCarry
  omega

end IsSuperadditiveRoof

namespace HasUnitCarry

/-- exact addition formula。 -/
theorem add_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    β (a + b) = β a + β b + roofCarry β a b :=
  U.lower.add_eq a b

/-- carry は高々 `1`。 -/
theorem carry_le_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry β a b ≤ 1 := by
  have hLower := U.lower a b
  have hUpper := U.upper a b
  unfold roofCarry
  omega

/-- carry は exact に `0` または `1`。 -/
theorem carry_eq_zero_or_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry β a b = 0 ∨ roofCarry β a b = 1 := by
  have h := U.carry_le_one a b
  omega

/-- 左幅 `0` の carry は `0`。 -/
@[simp] theorem carry_zero_left
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ) :
    roofCarry β 0 a = 0 := by
  simp [roofCarry, U.zero_eq]

/-- 右幅 `0` の carry は `0`。 -/
@[simp] theorem carry_zero_right
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ) :
    roofCarry β a 0 = 0 := by
  simp [roofCarry, U.zero_eq]

/--
carry cocycle。

`c(a,b) + c(a+b,d) = c(b,d) + c(a,b+d)`。
-/
theorem carry_cocycle
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b d : ℕ) :
    roofCarry β a b + roofCarry β (a + b) d =
      roofCarry β b d + roofCarry β a (b + d) := by
  have hAB := U.add_eq a b
  have hAB_D := U.add_eq (a + b) d
  have hBD := U.add_eq b d
  have hA_BD := U.add_eq a (b + d)
  have hAssoc : (a + b) + d = a + (b + d) := by omega
  rw [hAssoc] at hAB_D
  omega

end HasUnitCarry
end Experimental2
end Collatz3
