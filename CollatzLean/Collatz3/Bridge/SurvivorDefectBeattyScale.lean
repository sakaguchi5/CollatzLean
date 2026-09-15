import CollatzLean.Collatz3.Bridge.SurvivorDefectNormalizedActual
import CollatzLean.Collatz3.Bridge.SurvivorCompletionLift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: defect-normalized actual value の Beatty scale 表示

既存 exact bridge

`V_m = R_m * 3^m / 2^(beattyIndex m + 2)`

から、純粋な Beatty scale

`P_m = 3^m / 2^(beattyIndex m)`

だけを切り出す。

power-form Beatty bounds により常に

`1 ≤ P_m < 2`

であり、exact に

`V_m = (R_m / 4) * P_m`

となる。したがって `R_m` が有限実数 `L` に近いほど、`V_m` は
`(L/4) P_m` に同じ誤差スケールで近い。

新しい orbit notion は導入しない。Beatty roof だけから読む scalar scale 一個だけを置く。
-/

namespace Collatz3
namespace Bridge

/-- `3^m` を Beatty lower roof `2^beattyIndex(m)` で割った scale。 -/
noncomputable def survivorBeattyScale (m : ℕ) : ℝ :=
  (3 : ℝ) ^ m / (2 : ℝ) ^ Critical.beattyIndex m

/-- Beatty scale は常に `[1,2)` に入る。 -/
theorem survivorBeattyScale_mem_Ico_one_two
    (m : ℕ) :
    1 ≤ survivorBeattyScale m ∧ survivorBeattyScale m < 2 := by
  have hLowerNat := Critical.beattyIndex_lower m
  have hUpperNat := Critical.beattyIndex_upper m
  have hNeNat :
      3 ^ m ≠ 2 ^ (Critical.beattyIndex m + 1) := by
    intro hEq
    rcases threePow_odd_nat m with ⟨q, hq⟩
    rw [hq] at hEq
    rw [pow_succ] at hEq
    have hp := Arithmetic.twoPow_pos (Critical.beattyIndex m)
    omega
  have hUpperStrictNat :
      3 ^ m < 2 ^ (Critical.beattyIndex m + 1) :=
    lt_of_le_of_ne hUpperNat hNeNat
  have hLower :
      (2 : ℝ) ^ Critical.beattyIndex m ≤ (3 : ℝ) ^ m := by
    exact_mod_cast hLowerNat
  have hUpper :
      (3 : ℝ) ^ m < (2 : ℝ) ^ (Critical.beattyIndex m + 1) := by
    exact_mod_cast hUpperStrictNat
  have hDen : (0 : ℝ) < (2 : ℝ) ^ Critical.beattyIndex m := by positivity
  constructor
  · unfold survivorBeattyScale
    exact (le_div_iff₀ hDen).2 (by simpa using hLower)
  · unfold survivorBeattyScale
    apply (div_lt_iff₀ hDen).2
    rw [pow_succ] at hUpper
    nlinarith

end Bridge

namespace OddOrbit

open Bridge
open Filter

/--
`V_m` の exact Beatty-scale factorization。

`V_m = (R_m / 4) * P_m`。
-/
theorem defectNormalizedActualValue_eq_escape_div_four_mul_beattyScale
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.defectNormalizedActualValue m =
      (O.normalizedEscapeCoordinate m / 4) * survivorBeattyScale m := by
  rw [O.defectNormalizedActualValue_eq_escape_mul_threePow_div_beatty SInf m]
  unfold survivorBeattyScale
  rw [show Critical.beattyIndex m + 2 = Critical.beattyIndex m + 2 by rfl,
    pow_add]
  norm_num
  field_simp

/--
任意の実数 `L` に対する target discrepancy の exact factorization。

`V_m - (L/4)P_m = ((R_m-L)/4)P_m`。
-/
theorem defectNormalizedActualValue_sub_limitBeattyTarget_eq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (L : ℝ)
    (m : ℕ) :
    O.defectNormalizedActualValue m - (L / 4) * survivorBeattyScale m =
      ((O.normalizedEscapeCoordinate m - L) / 4) * survivorBeattyScale m := by
  rw [O.defectNormalizedActualValue_eq_escape_div_four_mul_beattyScale SInf m]
  ring

/--
Beatty scale が `<2` なので、`V_m` の target error は `R_m` の error の半分以下。

これは `R_m -> L` から `V_m` が moving Beatty target `(L/4)P_m` へ近づくことの
pointwise quantitative core。
-/
theorem abs_defectNormalizedActualValue_sub_limitBeattyTarget_le
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (L : ℝ)
    (m : ℕ) :
    |O.defectNormalizedActualValue m - (L / 4) * survivorBeattyScale m| ≤
      |O.normalizedEscapeCoordinate m - L| / 2 := by
  rw [O.defectNormalizedActualValue_sub_limitBeattyTarget_eq SInf L m]
  have hP := survivorBeattyScale_mem_Ico_one_two m
  have hPNonneg : 0 ≤ survivorBeattyScale m := by linarith [hP.1]
  rw [abs_mul, abs_div]
  rw [abs_of_nonneg hPNonneg]
  norm_num
  have hAbs : 0 ≤ |O.normalizedEscapeCoordinate m - L| := abs_nonneg _
  nlinarith

/--
`R_m -> L` なら `V_m` は moving Beatty target `(L/4)P_m` に漸近する。

`P_m` 自体の収束は仮定しない。`1 ≤ P_m < 2` という一様 bound と
前定理の error estimate だけを使う。
-/
theorem defectNormalizedActualValue_sub_limitBeattyTarget_tendsto_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun m : ℕ =>
        O.defectNormalizedActualValue m - (L / 4) * survivorBeattyScale m)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hT ⊢
  intro ε hε
  rcases hT (2 * ε) (by linarith) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hRn := hN n hn
  rw [Real.dist_eq] at hRn ⊢
  have hBound :=
    O.abs_defectNormalizedActualValue_sub_limitBeattyTarget_le SInf L n
  simp only [sub_zero] at ⊢
  nlinarith

end OddOrbit
end Collatz3
