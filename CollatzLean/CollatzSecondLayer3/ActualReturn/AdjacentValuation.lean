import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentState
import CollatzLean.CollatzSecondLayer3.ActualReturn.Valuation

/-!
# adjacent future-minimum valuation triangle

旧 first-crossing valuation triangle の純 `ExactTwoFactor` 補題を、
隣接する標準 future-minimum

`x < y`, `Δ = y-x`

へ直接再利用する。

`A = v2(x+1)`, `C = v2(y+1)`, `D = v2(Δ)` とすると

* `A < C -> D = A`
* `C < A -> D = C`
* `A = C -> A < D`

である。両 endpoint は future-minimum なので `A,C >= 2`、従って `D >= 2`。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer

namespace AdjacentFutureMinimumReturnData

/-- current future-minimum の `x+1` 完全2進分解。 -/
noncomputable def startPlusOneFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ReturnExactTwoFactorData (R.startValue + 1) :=
  returnExactTwoFactorData
    (R.startValue + 1)
    (by have := O.value_pos R.startIndex; unfold startValue; omega)

/-- next future-minimum の `y+1` 完全2進分解。 -/
noncomputable def nextPlusOneFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ReturnExactTwoFactorData (R.nextValue + 1) :=
  returnExactTwoFactorData
    (R.nextValue + 1)
    (by have := O.value_pos R.nextIndex; unfold nextValue; omega)

/-- 隣接値差 `Δ` の完全2進分解。 -/
noncomputable def valueGapFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ReturnExactTwoFactorData R.valueGap :=
  returnExactTwoFactorData R.valueGap R.valueGap_pos

/-- `A = v2(x+1)`。 -/
noncomputable def startPlusOneDepth
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  R.startPlusOneFactor.exponent

/-- `C = v2(y+1)`。 -/
noncomputable def nextPlusOneDepth
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  R.nextPlusOneFactor.exponent

/-- `D = v2(Δ)`。 -/
noncomputable def valueGapDepth
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  R.valueGapFactor.exponent

/-- current `x+1` の exact factorization。 -/
theorem startPlusOne_exactFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ExactTwoFactor
      (R.startValue + 1)
      R.startPlusOneDepth
      R.startPlusOneFactor.oddPart :=
  R.startPlusOneFactor.factorization

/-- next `y+1` の exact factorization。 -/
theorem nextPlusOne_exactFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ExactTwoFactor
      (R.nextValue + 1)
      R.nextPlusOneDepth
      R.nextPlusOneFactor.oddPart :=
  R.nextPlusOneFactor.factorization

/-- `Δ` の exact factorization。 -/
theorem valueGap_exactFactor
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    ExactTwoFactor
      R.valueGap
      R.valueGapDepth
      R.valueGapFactor.oddPart :=
  R.valueGapFactor.factorization

/-- 両 `+1` の正差は `Δ` そのもの。 -/
theorem plusOne_difference_eq_valueGap
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    (R.nextValue + 1) - (R.startValue + 1) = R.valueGap := by
  rw [R.nextValue_eq_startValue_add_valueGap]
  omega

/-- current future-minimum の `x+1` depth は2以上。 -/
theorem startPlusOneDepth_two_le
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    2 ≤ R.startPlusOneDepth := by
  unfold startPlusOneDepth
  have hmin : O.FutureMinimumAt R.startIndex := by
    simpa [startIndex] using O.futureMinimumAt_futureMinIndex R.index
  have hfac :
      ExactTwoFactor
        (O.value R.startIndex + 1)
        R.startPlusOneFactor.exponent
        R.startPlusOneFactor.oddPart := by
    simpa [startValue] using R.startPlusOneFactor.factorization
  exact futureMinimum_plusOne_exactDepth_two_le
    O R.unbounded hmin hfac

/-- next future-minimum の `y+1` depth も2以上。 -/
theorem nextPlusOneDepth_two_le
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    2 ≤ R.nextPlusOneDepth := by
  unfold nextPlusOneDepth
  have hmin : O.FutureMinimumAt R.nextIndex := by
    simpa [nextIndex] using O.futureMinimumAt_futureMinIndex (R.index + 1)
  have hfac :
      ExactTwoFactor
        (O.value R.nextIndex + 1)
        R.nextPlusOneFactor.exponent
        R.nextPlusOneFactor.oddPart := by
    simpa [nextValue] using R.nextPlusOneFactor.factorization
  exact futureMinimum_plusOne_exactDepth_two_le
    O R.unbounded hmin hfac

/-- `A<C` なら `D=A`。 -/
theorem valueGapDepth_eq_startDepth_of_lt
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    (hAC : R.startPlusOneDepth < R.nextPlusOneDepth) :
    R.valueGapDepth = R.startPlusOneDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    rw [R.nextValue_eq_startValue_add_valueGap]
    have hpos := R.valueGap_pos
    omega
  have hD :
      ExactTwoFactor
        ((R.nextValue + 1) - (R.startValue + 1))
        R.valueGapDepth
        R.valueGapFactor.oddPart := by
    rw [R.plusOne_difference_eq_valueGap]
    exact R.valueGap_exactFactor
  exact exactTwoFactor_sub_depth_eq_left_of_lt
    R.startPlusOne_exactFactor R.nextPlusOne_exactFactor hD hXY hAC

/-- `C<A` なら `D=C`。 -/
theorem valueGapDepth_eq_nextDepth_of_lt
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    (hCA : R.nextPlusOneDepth < R.startPlusOneDepth) :
    R.valueGapDepth = R.nextPlusOneDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    rw [R.nextValue_eq_startValue_add_valueGap]
    have hpos := R.valueGap_pos
    omega
  have hD :
      ExactTwoFactor
        ((R.nextValue + 1) - (R.startValue + 1))
        R.valueGapDepth
        R.valueGapFactor.oddPart := by
    rw [R.plusOne_difference_eq_valueGap]
    exact R.valueGap_exactFactor
  exact exactTwoFactor_sub_depth_eq_right_of_lt
    R.startPlusOne_exactFactor R.nextPlusOne_exactFactor hD hXY hCA

/-- `A=C` なら共通 depth より `Δ` の depth が真に深い。 -/
theorem startDepth_lt_valueGapDepth_of_eq
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    (hEq : R.startPlusOneDepth = R.nextPlusOneDepth) :
    R.startPlusOneDepth < R.valueGapDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    rw [R.nextValue_eq_startValue_add_valueGap]
    have hpos := R.valueGap_pos
    omega
  have hNext :
      ExactTwoFactor
        (R.nextValue + 1)
        R.startPlusOneDepth
        R.nextPlusOneFactor.oddPart := by
    rw [hEq]
    exact R.nextPlusOne_exactFactor
  have hD :
      ExactTwoFactor
        ((R.nextValue + 1) - (R.startValue + 1))
        R.valueGapDepth
        R.valueGapFactor.oddPart := by
    rw [R.plusOne_difference_eq_valueGap]
    exact R.valueGap_exactFactor
  exact exactTwoFactor_sub_depth_gt_of_eq
    R.startPlusOne_exactFactor hNext hD hXY

/-- 隣接 future-minimum 値差の exact 2進 depth は常に2以上。 -/
theorem valueGapDepth_two_le
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O) :
    2 ≤ R.valueGapDepth := by
  rcases lt_trichotomy R.startPlusOneDepth R.nextPlusOneDepth with hAC | hEq | hCA
  · rw [R.valueGapDepth_eq_startDepth_of_lt hAC]
    exact R.startPlusOneDepth_two_le
  · have hgt := R.startDepth_lt_valueGapDepth_of_eq hEq
    exact le_trans R.startPlusOneDepth_two_le (Nat.le_of_lt hgt)
  · rw [R.valueGapDepth_eq_nextDepth_of_lt hCA]
    exact R.nextPlusOneDepth_two_le

end AdjacentFutureMinimumReturnData

end CollatzSecondLayer3
