import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiCoordinates
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: Ostrowski convergent length の actual log-phase near return

`BeattyRegularOstrowskiSystem` の shifted `(P,Q)` は

`Q/P ≈ log₂3`

を与える。従って同じ denominator `P` は

`P * log₂(3/2) ≈ Q-P ∈ ℤ`

を満たし、actual Collatz log-phase の近回帰時間になる。

このファイルでは

1. horizontal weight `P_(n+1)` に対する rotation error を定義する。
2. Farey determinant `±1` からその absolute error が次 weight の逆数未満であることを導く。
3. `Runs` の odd-step 数がその horizontal weight に一致するとき、actual phase を
   `rotation error + correction sum` だけで exact に書く。
4. run が全区間で `X` 以上なら total shift を
   `1/q_next + q/(3X ln 2)` で評価する。

RecordFerrers block との一致はまだ仮定・主張しない。
-/

namespace Collatz3
open Experimental2
namespace Bridge

namespace BeattyRegularOstrowskiSystem

/--
`n` 番目 horizontal weight `P_(n+1)` 回の pure rotation が整数 `Q_(n+1)-P_(n+1)`
からどれだけずれるか。
-/
noncomputable def horizontalRotationReturnError
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) : ℝ :=
  ((D.horizontalWeights).Q n : ℝ) * collatzLogRotation -
    ((((D.conv.Q (n + 1) : ℤ) - (D.conv.P (n + 1) : ℤ) : ℤ)) : ℝ)

/-- return error は `P_(n+1) * log₂3 - Q_(n+1)` と exact に同じ。 -/
theorem horizontalRotationReturnError_eq_logb_error
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) :
    D.horizontalRotationReturnError n =
      (D.conv.P (n + 1) : ℝ) * Real.logb 2 3 -
        (D.conv.Q (n + 1) : ℝ) := by
  unfold horizontalRotationReturnError
  rw [D.horizontalWeights_Q n]
  rw [collatzLogRotation_eq_logb_three_sub_one]
  push_cast
  ring

/--
continued-fraction/Farey bracket の determinant `±1` から、horizontal rotation return error は
次の horizontal weight の逆数より strict に小さい。
-/
theorem abs_horizontalRotationReturnError_lt_inv_nextWeight
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) :
    |D.horizontalRotationReturnError n| <
      1 / ((D.horizontalWeights).Q (n + 1) : ℝ) := by
  rw [D.horizontalRotationReturnError_eq_logb_error n]
  rw [D.horizontalWeights_Q (n + 1)]
  have hmod : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by
    have hlt := Nat.mod_lt (n + 1) (by omega : 0 < 2)
    omega
  rcases hmod with hEven | hOdd
  · rcases D.lowerBracket (n + 1) hEven with
      ⟨hP, hPn, hCurrent, hNext, hDet⟩
    have hPR : (0 : ℝ) < (D.conv.P (n + 1) : ℝ) := by
      exact_mod_cast hP
    have hPnR : (0 : ℝ) < (D.conv.P (n + 2) : ℝ) := by
      exact_mod_cast hPn
    have hCurrentMul :
        (D.conv.Q (n + 1) : ℝ) <
          Real.logb 2 3 * (D.conv.P (n + 1) : ℝ) :=
      (div_lt_iff₀ hPR).1 hCurrent
    have hNextMul :
        Real.logb 2 3 * (D.conv.P (n + 2) : ℝ) <
          (D.conv.Q (n + 2) : ℝ) :=
      (lt_div_iff₀ hPnR).1 hNext
    have hNextScaled :=
      mul_lt_mul_of_pos_left hNextMul hPR
    have hDetR :
        (D.conv.P (n + 2) : ℝ) * (D.conv.Q (n + 1) : ℝ) + 1 =
          (D.conv.P (n + 1) : ℝ) * (D.conv.Q (n + 2) : ℝ) := by
      exact_mod_cast hDet
    have hErrPos :
        0 < (D.conv.P (n + 1) : ℝ) * Real.logb 2 3 -
          (D.conv.Q (n + 1) : ℝ) := by
      nlinarith
    have hErrUpper :
        (D.conv.P (n + 1) : ℝ) * Real.logb 2 3 -
            (D.conv.Q (n + 1) : ℝ) <
          1 / (D.conv.P (n + 2) : ℝ) := by
      apply (lt_div_iff₀ hPnR).2
      nlinarith [hNextScaled, hDetR]
    rw [abs_of_pos hErrPos]
    exact hErrUpper
  · rcases D.upperBracket (n + 1) hOdd with
      ⟨hP, hPn, hNext, hCurrent, hDet⟩
    have hPR : (0 : ℝ) < (D.conv.P (n + 1) : ℝ) := by
      exact_mod_cast hP
    have hPnR : (0 : ℝ) < (D.conv.P (n + 2) : ℝ) := by
      exact_mod_cast hPn
    have hCurrentMul :
        Real.logb 2 3 * (D.conv.P (n + 1) : ℝ) <
          (D.conv.Q (n + 1) : ℝ) :=
      (lt_div_iff₀ hPR).1 hCurrent
    have hNextMul :
        (D.conv.Q (n + 2) : ℝ) <
          Real.logb 2 3 * (D.conv.P (n + 2) : ℝ) :=
      (div_lt_iff₀ hPnR).1 hNext
    have hNextScaled :=
      mul_lt_mul_of_pos_left hNextMul hPR
    have hDetR :
        (D.conv.P (n + 1) : ℝ) * (D.conv.Q (n + 2) : ℝ) + 1 =
          (D.conv.P (n + 2) : ℝ) * (D.conv.Q (n + 1) : ℝ) := by
      exact_mod_cast hDet
    have hErrNeg :
        (D.conv.P (n + 1) : ℝ) * Real.logb 2 3 -
          (D.conv.Q (n + 1) : ℝ) < 0 := by
      nlinarith
    have hAbsUpper :
        (D.conv.Q (n + 1) : ℝ) -
            (D.conv.P (n + 1) : ℝ) * Real.logb 2 3 <
          1 / (D.conv.P (n + 2) : ℝ) := by
      apply (lt_div_iff₀ hPnR).2
      nlinarith [hNextScaled, hDetR]
    rw [abs_of_neg hErrNeg]
    nlinarith

end BeattyRegularOstrowskiSystem

end Bridge

namespace Runs

/--
run 長が horizontal convergent denominator と一致する場合の exact near-return phase formula。

pure rotation の整数部分を fractional part から落とすと、残る shift は

`rotationReturnError + logCorrectionSum`

だけである。
-/
theorem logPhase_horizontalNearReturn
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (n : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = (D.horizontalWeights).Q n) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x +
          D.horizontalRotationReturnError n +
          h.logCorrectionSum) := by
  rw [h.logPhase_run]
  rw [hSteps]
  let k : ℤ :=
    (D.conv.Q (n + 1) : ℤ) - (D.conv.P (n + 1) : ℤ)
  have hSplit :
      ((D.horizontalWeights).Q n : ℝ) * Bridge.collatzLogRotation =
        D.horizontalRotationReturnError n + (k : ℝ) := by
    unfold Bridge.BeattyRegularOstrowskiSystem.horizontalRotationReturnError
    dsimp [k]
    ring
  rw [hSplit]
  calc
    Int.fract
        (Bridge.collatzLogPhase x +
          (D.horizontalRotationReturnError n + (k : ℝ)) +
          h.logCorrectionSum) =
      Int.fract
        ((Bridge.collatzLogPhase x +
            D.horizontalRotationReturnError n +
            h.logCorrectionSum) + (k : ℝ)) := by
          congr 1
          ring
    _ = Int.fract
        (Bridge.collatzLogPhase x +
          D.horizontalRotationReturnError n +
          h.logCorrectionSum) := by
          rw [Int.fract_add_intCast]

/--
高い軌道区間上の near-return shift の absolute bound。

`q = horizontalWeight n`, `q_next = horizontalWeight (n+1)` とすると

`|error + Σδ| < 1/q_next + q/(3X ln 2)`。
-/
theorem horizontalNearReturnShift_abs_lt
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (n X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = (D.horizontalWeights).Q n)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x) :
    |D.horizontalRotationReturnError n + h.logCorrectionSum| <
      1 / ((D.horizontalWeights).Q (n + 1) : ℝ) +
        ((D.horizontalWeights).Q n : ℝ) /
          (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  have hErr :=
    D.abs_horizontalRotationReturnError_lt_inv_nextWeight n
  have hSumNonneg :=
    h.logCorrectionSum_nonneg
  have hSum :=
    h.logCorrectionSum_le_steps_div_three_mul_log_two hX hAbove
  rw [hSteps] at hSum
  have hTriangle :
      |D.horizontalRotationReturnError n + h.logCorrectionSum| ≤
        |D.horizontalRotationReturnError n| +
          |h.logCorrectionSum| :=
    abs_add_le _ _
  rw [abs_of_nonneg hSumNonneg] at hTriangle
  calc
    |D.horizontalRotationReturnError n + h.logCorrectionSum|
        ≤ |D.horizontalRotationReturnError n| +
            h.logCorrectionSum :=
      hTriangle
    _ < 1 / ((D.horizontalWeights).Q (n + 1) : ℝ) +
          h.logCorrectionSum := by
      simpa [add_comm] using
        add_lt_add_right hErr h.logCorrectionSum
    _ ≤ 1 / ((D.horizontalWeights).Q (n + 1) : ℝ) +
          ((D.horizontalWeights).Q n : ℝ) /
            (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
      exact
        add_le_add_right hSum
          (1 / ((D.horizontalWeights).Q (n + 1) : ℝ))

/--
exact phase formula と near-return bound を一つに束ねた第三段の最終 API。

この theorem は `q`-step block が RecordFerrers canonical block と一致するとは主張しない。
-/
theorem logPhase_horizontalNearReturn_with_bound
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (n X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = (D.horizontalWeights).Q n)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x) :
    Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            D.horizontalRotationReturnError n +
            h.logCorrectionSum) ∧
      |D.horizontalRotationReturnError n + h.logCorrectionSum| <
        1 / ((D.horizontalWeights).Q (n + 1) : ℝ) +
          ((D.horizontalWeights).Q n : ℝ) /
            (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  exact
    ⟨h.logPhase_horizontalNearReturn D n hSteps,
      h.horizontalNearReturnShift_abs_lt
        D n X hSteps hX hAbove⟩

end Runs
end Collatz3
