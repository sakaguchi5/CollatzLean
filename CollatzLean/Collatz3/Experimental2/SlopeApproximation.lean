import CollatzLean.Collatz3.Experimental2.SlopeWindow
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp

/-!
# Collatz3 Experimental2: 計算可能な slope 近似

exact Real slope 自体を executable data にせず、
有限幅 `N+1` から得る有理数上下界だけを計算可能にする。
-/

namespace Collatz3
namespace Experimental2

/-- `N+1` 幅から得る計算可能な下側 slope 近似。 -/
def lowerSlopeApprox
    (β : ℕ → ℕ)
    (N : ℕ) : ℚ :=
  (β (N + 1) : ℚ) / ((N + 1 : ℕ) : ℚ)

/-- `N+1` 幅から得る計算可能な上側 slope 近似。 -/
def upperSlopeApprox
    (β : ℕ → ℕ)
    (N : ℕ) : ℚ :=
  ((β (N + 1) : ℚ) + 1) / ((N + 1 : ℕ) : ℚ)

/-- 上下近似の差は exact に `1/(N+1)`。 -/
theorem upperSlopeApprox_sub_lowerSlopeApprox
    (β : ℕ → ℕ)
    (N : ℕ) :
    upperSlopeApprox β N - lowerSlopeApprox β N =
      1 / ((N + 1 : ℕ) : ℚ) := by
  unfold upperSlopeApprox lowerSlopeApprox
  have hne : (((N + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp
  ring

/-- lower 近似は upper 近似以下。 -/
theorem lowerSlopeApprox_le_upperSlopeApprox
    (β : ℕ → ℕ)
    (N : ℕ) :
    lowerSlopeApprox β N ≤ upperSlopeApprox β N := by
  unfold lowerSlopeApprox upperSlopeApprox
  have hpos : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) := by positivity
  exact div_le_div_of_nonneg_right (by norm_num) hpos.le

end Experimental2
end Collatz3
