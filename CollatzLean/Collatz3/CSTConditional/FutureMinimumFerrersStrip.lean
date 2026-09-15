import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoofAsymptotics
import CollatzLean.Collatz3.Bridge.FerrersCriticalEscapeWeight
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: local roof deficit と weighted Ferrers strip

前段では future minimum `start` から見た row `r` について

`c_start(r) = criticalEscapeWeight r / 2^(localRoofDefect start r)`

を導入し、A 型の normalized escape limit が存在すれば

`average (criticalEscapeWeight r - c_start(r)) -> 1 / (6 log 2)`

まで得た。

このファイルでは、その差を Ferrers の縦方向 cell weight の有限和として exact に読む。
新しい shape / path / orbit packet は導入しない。追加するのは、既存
`FerrersCriticalEscapeWeight` の 1-cell formula と同じ dyadic scale を持つ一つの scalar weight だけ。

zero-based の cell depth `s` に対して

`verticalCellWeight(r,s) = w_r / 2^(s+1)`

と置く。local roof defect が `d` なら、roof と actual profile の間の `d` 個の縦 cell は
`s = 0,...,d-1` であり、

`sum_{s<d} w_r / 2^(s+1) = w_r - w_r / 2^d`

が exact に成り立つ。

さらに既存 Ferrers 1-cell の roof defect が `s+1` なら、その normalized affine weight は
この `verticalCellWeight(r,s)` と exact に一致する。
-/

namespace Collatz3

open Bridge
open CSTConditional
open Filter
open scoped Topology BigOperators Real

/--
row `r` の roof から zero-based depth `s` にある縦 Ferrers cell の normalized weight。

`s=0` が roof 直下の最初の cell で、重みは `w_r/2`。
-/
noncomputable def criticalVerticalCellWeight
    (r s : ℕ) : ℝ :=
  criticalEscapeWeight r / (2 : ℝ) ^ (s + 1)

namespace Word

/--
既存 Ferrers 1-cell の roof defect が `s+1` なら、その normalized affine weight は
`criticalVerticalCellWeight row s` に exact に一致する。

従って `criticalVerticalCellWeight` は新しい恣意的な重みではなく、既存の
Ferrers affine cell weight を縦 depth で読み直したもの。
-/
theorem ferrersCellAffineWeight_div_threePow_total_eq_criticalVerticalCellWeight
    (u v : Word)
    (a s : ℕ)
    (hRoof :
      twoSteps u + a ≤ Critical.beattyIndex (oddSteps u + 1))
    (hDepth :
      Critical.beattyIndex (oddSteps u + 1) - (twoSteps u + a) = s + 1) :
    (ferrersCellAffineWeight u v a : ℝ) /
        (3 : ℝ) ^ (oddSteps u + 2 + oddSteps v) =
      criticalVerticalCellWeight (oddSteps u + 1) s := by
  rw [ferrersCellAffineWeight_div_threePow_total_eq_criticalEscapeWeight
    u v a hRoof]
  rw [hDepth]
  rfl

end Word

/--
同じ row の最初の `d` 個の縦 cell weight の和は、roof weight と depth `d` の
attenuated weight の差に exact に一致する。
-/
theorem criticalVerticalCellWeight_sum_range
    (r d : ℕ) :
    (∑ s ∈ Finset.range d, criticalVerticalCellWeight r s) =
      criticalEscapeWeight r -
        criticalEscapeWeight r / (2 : ℝ) ^ d := by
  induction d with
  | zero =>
      simp [criticalVerticalCellWeight]
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      unfold criticalVerticalCellWeight
      rw [pow_succ]
      field_simp
      ring

namespace OddOrbit

/--
row `r` の weighted roof deficit は、その row で roof と actual profile の間にある
縦 Ferrers cell weight の exact finite sum。

`d = futureMinimum_localRoofDefect start r` とすると

`w_r - c_start(r) = sum_{s<d} w_r / 2^(s+1)`。
-/
theorem weightedRoofDeficit_eq_verticalFerrersCellSum
    (O : Collatz3.OddOrbit)
    (start r : ℕ) :
    criticalEscapeWeight r -
        O.futureMinimumLocalRoofContribution start r =
      ∑ s ∈ Finset.range (O.futureMinimum_localRoofDefect start r),
        criticalVerticalCellWeight r s := by
  have h :=
    criticalVerticalCellWeight_sum_range
      r (O.futureMinimum_localRoofDefect start r)
  unfold futureMinimumLocalRoofContribution
  exact h.symm

/--
最初の `N` rows の weighted roof deficit は、各 row の縦 Ferrers strip weight を
全部足した二重有限和に exact に一致する。

これが finite weighted roof deficit と finite weighted Ferrers strip area の exact bridge。
-/
theorem weightedRoofDeficit_sum_range_eq_verticalFerrersStrip
    (O : Collatz3.OddOrbit)
    (start N : ℕ) :
    (∑ r ∈ Finset.range N,
        (criticalEscapeWeight r -
          O.futureMinimumLocalRoofContribution start r)) =
      ∑ r ∈ Finset.range N,
        ∑ s ∈ Finset.range (O.futureMinimum_localRoofDefect start r),
          criticalVerticalCellWeight r s := by
  apply Finset.sum_congr rfl
  intro r _hr
  exact O.weightedRoofDeficit_eq_verticalFerrersCellSum start r

/--
A 型 route で既に得た weighted roof deficit の Cesàro 極限を、
weighted Ferrers strip area の Cesàro 極限へ exact に移す。

従って normalized escape limit を持つ Global-CST future minimum では、

`average(weighted vertical Ferrers strip area) -> 1/(6 log 2)`。
-/
theorem weightedVerticalFerrersStrip_cesaro
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun N : ℕ =>
        (∑ r ∈ Finset.range N,
          ∑ s ∈ Finset.range (O.futureMinimum_localRoofDefect start r),
            criticalVerticalCellWeight r s) / (N : ℝ))
      atTop
      (nhds (1 / (6 * Real.log 2))) := by
  have hDeficit := O.weightedRoofDeficit_cesaro G hStart hT
  have hFun :
      (fun N : ℕ =>
        (∑ r ∈ Finset.range N,
          ∑ s ∈ Finset.range (O.futureMinimum_localRoofDefect start r),
            criticalVerticalCellWeight r s) / (N : ℝ)) =
      (fun N : ℕ =>
        (∑ r ∈ Finset.range N,
          (criticalEscapeWeight r -
            O.futureMinimumLocalRoofContribution start r)) / (N : ℝ)) := by
    funext N
    rw [O.weightedRoofDeficit_sum_range_eq_verticalFerrersStrip start N]
  rw [hFun]
  exact hDeficit

end OddOrbit
end Collatz3
