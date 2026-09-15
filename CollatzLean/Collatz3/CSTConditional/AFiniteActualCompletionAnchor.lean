import CollatzLean.Collatz3.CSTConditional.ANormalizedCompletionAnchor
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import CollatzLean.Collatz3.Bridge.SurvivorDefectBeattyScale

/-!
# Collatz3 CSTConditional: A 型 real target と finite actual/Hensel compatibility の共通 anchor

既存 `ANormalizedCompletionAnchor` は、linear defect survivor について任意に遠い
future-minimum `n` で real shadow と consecutive natural completion lift を同時に与える。

ここでは a4bf... 以後の finite bridge を同じ anchor に追加する。

* `R_m -> L`
* `V_m - (L/4) P_m -> 0`
* `x_n mod 2^(δ_n+2)` は有限 future word の canonical start で決まる
* `canonicalResidue + 3^n t ≡ 2^(δ_n+1) mod 2^(δ_n+2)`
* `theta_n + (3^n/4) upsilon_n ∈ Z`

重要なのは、最後の二項が finite natural endpoint equation だけから出ていること。
real limit と 2進 completion の極限を同一視しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

/--
linear defect survivor では任意に遠い future-minimum anchor で、real moving target と
finite actual/Hensel compatibility が同時に成立する。
-/
theorem exists_futureMinimum_finiteActualCompletionCompatibility_after_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (start : ℕ) :
    ∃ L : ℝ,
      0 < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      Tendsto
        (fun m : ℕ =>
          O.defectNormalizedActualValue m - (L / 4) * survivorBeattyScale m)
        atTop (nhds 0) ∧
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
        start < n ∧
        O.FutureMinimumAt n ∧
        O.exponent n = 1 ∧
        O.endpointCompletionStart SInf hn =
          O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
        O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
          O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
        ((Word.canonicalStart
              (O.segmentWord n (infiniteSurvivorDefect O.exponent n + 2)) %
            2 ^ (infiniteSurvivorDefect O.exponent n + 2)) +
              3 ^ n * t ≡
            2 ^ (infiniteSurvivorDefect O.exponent n + 1)
            [MOD 2 ^ (infiniteSurvivorDefect O.exponent n + 2)]) ∧
        (∃ z : ℤ,
          O.defectActualResidueFraction n +
              ((3 : ℝ) ^ n / 4) *
                O.centeredNormalizedCompletionLiftCoefficient n t =
            (z : ℝ)) ∧
        |O.defectNormalizedActualValue n - (L / 4) * survivorBeattyScale n| ≤
          |O.normalizedEscapeCoordinate n - L| / 2 := by
  rcases
      O.exists_futureMinimum_shadow_and_normalizedCompletionBranch_after_of_linearDefect
        SInf hLinear start with
    ⟨L, hL, hT,
      n, hn, t, u,
      hStart, hMin, he,
      hStartT, hStartU,
      _hEndpointNorm, _hGap, _hFive, _hBranch⟩
  have hMoving :=
    O.defectNormalizedActualValue_sub_limitBeattyTarget_tendsto_zero SInf hT
  have hHensel :=
    O.endpointCompletion_futureCanonicalResidueHensel_modEq SInf hn hStartT
  have hCompat :=
    O.exists_integer_defectActualResidueFraction_add_scaled_centeredLift
      SInf hn hStartT
  have hError :=
    O.abs_defectNormalizedActualValue_sub_limitBeattyTarget_le SInf L n
  exact
    ⟨L, hL, hT, hMoving,
      n, hn, t, u,
      hStart, hMin, he,
      hStartT, hStartU,
      hHensel, hCompat, hError⟩

end OddOrbit
end Collatz3
