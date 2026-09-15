import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape
import CollatzLean.Collatz3.CSTConditional.ADefectNormalizedActual
import CollatzLean.Collatz3.Bridge.SurvivorDefectBeattyScale
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Collatz3 CSTConditional: A 型 actual normalized state の two-sided compactness

既存 A 型 package では

`V_m = value(m) / 2^(delta_m+2)`

に一様 upper bound を与えている。
一方 exact Beatty-scale factorization

`V_m = (R_m/4) * P_m`,  `1 <= P_m < 2`

と A 型 real limit `R_m -> L > 0` を合わせると、late tail では `V_m` は
0 に近付くこともできない。

ここでは新しい compact state を定義せず、既存 `V_m` に対して

`L/8 < V_m < L/2`

となる sufficiently late tail を derived theorem として切り出す。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

/--
linear defect survivor の defect-normalized actual state は sufficiently late に
positive compact annulus `(L/8, L/2)` へ入る。
-/
theorem exists_defectNormalizedActual_compactAnnulus_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    ∃ L : ℝ,
      0 < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      ∃ M : ℕ,
        ∀ m : ℕ,
          M ≤ m →
            L / 8 < O.defectNormalizedActualValue m ∧
              O.defectNormalizedActualValue m < L / 2 := by
  rcases O.exists_normalizedEscapeLimit_of_linearDefect SInf hLinear with
    ⟨L, hL, hT, _hUpper⟩
  have hMetric := hT
  rw [Metric.tendsto_atTop] at hMetric
  rcases hMetric (L / 2) (by linarith) with ⟨M, hM⟩
  refine ⟨L, hL, hT, M, ?_⟩
  intro m hm
  have hClose := hM m hm
  rw [Real.dist_eq] at hClose
  have hRLower : L / 2 < O.normalizedEscapeCoordinate m := by
    have hAbs := abs_lt.mp hClose
    linarith
  have hRUpper : O.normalizedEscapeCoordinate m < L :=
    O.normalizedEscapeCoordinate_lt_limit_of_tendsto hT m
  have hRPos : 0 < O.normalizedEscapeCoordinate m :=
    O.normalizedEscapeCoordinate_pos m
  have hScale := survivorBeattyScale_mem_Ico_one_two m
  have hMulLower :
      O.normalizedEscapeCoordinate m ≤
        O.normalizedEscapeCoordinate m * survivorBeattyScale m :=
    by
      simpa using
        mul_le_mul_of_nonneg_left hScale.1 hRPos.le
  have hMulUpper :
      O.normalizedEscapeCoordinate m * survivorBeattyScale m <
        O.normalizedEscapeCoordinate m * 2 :=
    mul_lt_mul_of_pos_left hScale.2 hRPos
  rw [O.defectNormalizedActualValue_eq_escape_div_four_mul_beattyScale SInf m]
  constructor <;> nlinarith

end OddOrbit
end Collatz3
