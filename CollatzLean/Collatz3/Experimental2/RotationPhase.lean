import CollatzLean.Collatz3.Experimental2.CarryCore
import CollatzLean.Collatz3.Experimental2.MechanicalRoof
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: direct roof の rotation phase

phase を residual ではなく屋根そのものから

`φ(n) = nσ - β(n)`

と定義する。

lower mechanical では `0 ≤ φ < 1`、
upper mechanical では `0 < φ ≤ 1` となり、
carry は phase 和の wrap と一致する。
-/

namespace Collatz3
namespace Experimental2

def roofPhase
    (β : ℕ → ℕ)
    (σ : ℝ)
    (n : ℕ) : ℝ :=
  (n : ℝ) * σ - (β n : ℝ)

theorem roofPhase_add
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (σ : ℝ)
    (a b : ℕ) :
    roofPhase β σ (a + b) =
      roofPhase β σ a + roofPhase β σ b -
        (roofCarry β a b : ℝ) := by
  have hAdd := U.add_eq a b
  have hCast :
      (β (a + b) : ℝ) =
        (β a : ℝ) + (β b : ℝ) + (roofCarry β a b : ℝ) := by
    exact_mod_cast hAdd
  unfold roofPhase
  push_cast
  rw [hCast]
  ring

namespace IsLowerMechanicalRoof

theorem phase_nonneg
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (n : ℕ) :
    0 ≤ roofPhase β σ n := by
  have h := (M n).1
  unfold roofPhase
  linarith

theorem phase_lt_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (n : ℕ) :
    roofPhase β σ n < 1 := by
  have h := (M n).2
  unfold roofPhase
  linarith

end IsLowerMechanicalRoof

namespace IsUpperMechanicalRoof

theorem phase_pos
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ)
    {n : ℕ}
    (hn : 0 < n) :
    0 < roofPhase β σ n := by
  have h := (M.2 n hn).1
  unfold roofPhase
  linarith

theorem phase_le_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ)
    {n : ℕ}
    (hn : 0 < n) :
    roofPhase β σ n ≤ 1 := by
  have h := (M.2 n hn).2
  unfold roofPhase
  linarith

end IsUpperMechanicalRoof

/-- lower convention: carry `1` iff phase 和が `1` 以上。 -/
theorem carry_eq_one_iff_lowerPhase_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (a b : ℕ) :
    roofCarry β a b = 1 ↔
      1 ≤ roofPhase β σ a + roofPhase β σ b := by
  have hPhase := roofPhase_add U σ a b
  have hEndNonneg := M.phase_nonneg (a + b)
  have hEndLt := M.phase_lt_one (a + b)
  constructor
  · intro hOne
    rw [hOne] at hPhase
    norm_num at hPhase
    linarith
  · intro hWrap
    rcases U.carry_eq_zero_or_one a b with hZero | hOne
    · rw [hZero] at hPhase
      norm_num at hPhase
      linarith
    · exact hOne

/-- upper convention: carry `1` iff phase 和が strict に `1` を越える。 -/
theorem carry_eq_one_iff_upperPhase_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ)
    (a b : ℕ) :
    roofCarry β a b = 1 ↔
      1 < roofPhase β σ a + roofPhase β σ b := by
  by_cases hab : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simp [roofPhase, U.zero_eq, U.carry_zero_left]
  · have habPos : 0 < a + b := Nat.pos_of_ne_zero hab
    have hPhase := roofPhase_add U σ a b
    have hEndPos := M.phase_pos habPos
    have hEndLe := M.phase_le_one habPos
    constructor
    · intro hOne
      rw [hOne] at hPhase
      norm_num at hPhase
      linarith
    · intro hWrap
      rcases U.carry_eq_zero_or_one a b with hZero | hOne
      · rw [hZero] at hPhase
        norm_num at hPhase
        linarith
      · exact hOne

end Experimental2
end Collatz3
