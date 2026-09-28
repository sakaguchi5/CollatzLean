import CollatzLean.Collatz3.CSTCarry.ShiftedBeattyBlock
import CollatzLean.Collatz3.Critical.RecordLocalGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: shifted record block の exact defect scaling

record block start `a` が global Beatty roof 上にあるとする。
local index `j` では global boundary height は

`beattyIndex a + shiftedBeattyIndex a j`

であり、actual height は

`beattyIndex a + localDepth h a j`。

従って各 column の defect は `2^beattyIndex a` を共通因子として持つ。
この row-level identity を finite weighted sum まで持ち上げる。
-/

namespace Collatz3
namespace CSTCarry

open Critical
open scoped BigOperators

/-- shifted local roof と local actual depth の一列 defect。 -/
def shiftedBeattyDefect
    (a j actual : ℕ) : ℕ :=
  2 ^ shiftedBeattyIndex a j - 2 ^ actual

/--
shifted defect は standard local defect と phase cell に exact 分解される。

`c = beattyCarry a j ∈ {0,1}` とすると

`2^(β_j+c)-2^e = (2^β_j-2^e) + c*2^β_j`。
-/
theorem shiftedBeattyDefect_eq_local_add_phase
    {a j actual : ℕ}
    (hActual : actual ≤ beattyIndex j) :
    shiftedBeattyDefect a j actual =
      (2 ^ beattyIndex j - 2 ^ actual) +
        beattyCarry a j * 2 ^ beattyIndex j := by
  rcases beattyCarry_eq_zero_or_one a j with hZero | hOne
  · simp [shiftedBeattyDefect, shiftedBeattyIndex_eq, hZero]
  · have hPowLe : 2 ^ actual ≤ 2 ^ beattyIndex j :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hActual
    have hShift :
        shiftedBeattyIndex a j = beattyIndex j + 1 := by
      rw [shiftedBeattyIndex_eq, hOne]
    unfold shiftedBeattyDefect
    rw [hShift, hOne, pow_succ]
    simp only [one_mul]
    omega

/--
一列の global boundary/actual difference を subtraction-free に factor した形。
-/
theorem globalBoundaryPow_eq_actualPow_add_scaled_shiftedDefect
    {a j actual : ℕ}
    (hActual : actual ≤ shiftedBeattyIndex a j) :
    2 ^ beattyIndex (a + j) =
      2 ^ (beattyIndex a + actual) +
        2 ^ beattyIndex a * shiftedBeattyDefect a j actual := by
  have hIndex :
      beattyIndex (a + j) =
        beattyIndex a + shiftedBeattyIndex a j := by
    rw [shiftedBeattyIndex_eq, beattyIndex_add_eq]
    omega
  have hPowLe :
      2 ^ actual ≤ 2 ^ shiftedBeattyIndex a j :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hActual
  have hSplit :
      2 ^ actual + shiftedBeattyDefect a j actual =
        2 ^ shiftedBeattyIndex a j := by
    unfold shiftedBeattyDefect
    simpa [Nat.add_comm] using Nat.sub_add_cancel hPowLe
  calc
    2 ^ beattyIndex (a + j)
        = 2 ^ beattyIndex a * 2 ^ shiftedBeattyIndex a j := by
            rw [hIndex, pow_add]
    _ = 2 ^ beattyIndex a *
          (2 ^ actual + shiftedBeattyDefect a j actual) := by
            rw [hSplit]
    _ = 2 ^ (beattyIndex a + actual) +
          2 ^ beattyIndex a * shiftedBeattyDefect a j actual := by
            rw [pow_add]
            ring

/--
roof start を持つ admissible profile に上の一列 scaling を特殊化した形。
-/
theorem profileBoundaryPow_eq_actualPow_add_scaled_shiftedDefect
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + j ≤ m)
    (hLocal : localDepth h a j ≤ beattyIndex j) :
    2 ^ beattyIndex (a + j) =
      2 ^ profileHeight h (a + j) +
        2 ^ beattyIndex a *
          shiftedBeattyDefect a j (localDepth h a j) := by
  have hShiftLe :
      localDepth h a j ≤ shiftedBeattyIndex a j :=
    le_trans hLocal (beattyIndex_le_shiftedBeattyIndex a j)
  have hScale :=
    globalBoundaryPow_eq_actualPow_add_scaled_shiftedDefect
      (a := a) (j := j) (actual := localDepth h a j) hShiftLe
  have hDepth := profileHeight_add_localDepth A hEnd
  rw [hStartRoof.height_eq] at hDepth
  rw [hDepth] at hScale
  exact hScale

/-- subtraction 版の一列 exact scaling。 -/
theorem profileColumnDefect_eq_scaled_shiftedBeattyDefect
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + j ≤ m)
    (hLocal : localDepth h a j ≤ beattyIndex j) :
    2 ^ beattyIndex (a + j) - 2 ^ profileHeight h (a + j) =
      2 ^ beattyIndex a *
        shiftedBeattyDefect a j (localDepth h a j) := by
  have hEq :=
    profileBoundaryPow_eq_actualPow_add_scaled_shiftedDefect
      A hStartRoof hEnd hLocal
  omega

/-- global block の weighted defect を direct finite sum で読む。 -/
def profileBlockWeightedDefect
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : ℕ :=
  Finset.sum (Finset.range r) (fun j =>
    3 ^ (r - (j + 1)) *
      (2 ^ beattyIndex (a + j) - 2 ^ profileHeight h (a + j)))


/-- start roof から相対化した shifted-local weighted defect。 -/
def shiftedBlockWeightedDefect
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : ℕ :=
  Finset.sum (Finset.range r) (fun j =>
    3 ^ (r - (j + 1)) *
      shiftedBeattyDefect a j (localDepth h a j))

/--
block 全体の exact scaling。

`global block defect = 2^beattyIndex(a) * shifted-local block defect`。
-/
theorem profileBlockWeightedDefect_eq_scaled_shifted
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hEnd : a + r ≤ m)
    (hPrefix :
      ∀ j : ℕ, j < r →
        localDepth h a j ≤ beattyIndex j) :
    profileBlockWeightedDefect h a r =
      2 ^ beattyIndex a * shiftedBlockWeightedDefect h a r := by
  unfold profileBlockWeightedDefect shiftedBlockWeightedDefect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjLt : j < r := Finset.mem_range.mp hj
  have hWithin : a + j ≤ m := by
    omega
  have hDef :=
    profileColumnDefect_eq_scaled_shiftedBeattyDefect
      A hStartRoof hWithin (hPrefix j hjLt)
  rw [hDef]
  ring

/-- local critical block では prefix hypothesis を structure から自動供給できる。 -/
theorem profileBlockWeightedDefect_eq_scaled_shifted_of_localCritical
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r) :
    profileBlockWeightedDefect h a r =
      2 ^ beattyIndex a * shiftedBlockWeightedDefect h a r := by
  apply profileBlockWeightedDefect_eq_scaled_shifted
    A hStartRoof B.2.1
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [localDepth]
  · exact B.2.2.2 j (Nat.pos_of_ne_zero hj0) hj

/--
terminal carry `0` の block では global strict budget を shifted-local budget へ exact に縮約できる。

ここでは ternary complement value を抽象変数 `D` として保持する。
-/
theorem terminalBlock_strictBudget_iff_shiftedLocal
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r D : ℕ}
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r)
    (hTerminal : a + r = m)
    (hCarryZero : beattyCarry a r = 0) :
    profileBlockWeightedDefect h a r <
        2 ^ criticalTwoDepth m * (D + 1) ↔
      shiftedBlockWeightedDefect h a r <
        2 ^ criticalTwoDepth r * (D + 1) := by
  have hS :=
    profileBlockWeightedDefect_eq_scaled_shifted_of_localCritical
      A hStartRoof B
  have hM :=
    twoPow_criticalTwoDepth_eq_mul_of_terminal_carry_zero
      hTerminal hCarryZero
  rw [hS, hM]
  exact scaled_strictBudget_iff (by positivity)

end CSTCarry
end Collatz3
