import CollatzLean.Collatz3.CSTConditional.ANormalizedEscapeShadow
import CollatzLean.Collatz3.Bridge.SurvivorCompletionNormalizedLift
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeCompletion
import CollatzLean.Collatz3.Bridge.SurvivorCompletionFutureMinimum

/-!
# Collatz3 CSTConditional: A 型 real shadow と normalized completion branch の同一 anchor 上での共存

A 型の量的条件 `LinearDefectLowerBound` から得られる real escape limit / negative shadow と、
既存 completion Hensel lift は別々の completion であり、ここでは両者を同一視しない。

このファイルで行うのは、任意に遠い actual future-minimum anchor `n` を一つ選び、
その同じ `n` で

* real shadow gap `-Z_n > 0`,
* consecutive natural completion lifts `t_n,t_(n+1)`,
* defect-normalized cocycle の fixed 5 branch,
* local defect flat / rise に応じた `2 tau'-tau` / `4 tau'-tau` の exact 式

が同時に成立することを束ねるだけである。

これは real limit と 2進 completion の「矛盾」を主張する theorem ではない。
今後有限 branch ごとに real affine constraint を重ねるための共通 anchor theorem である。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

/--
linear defect survivor では任意に遠い future-minimum anchor で、negative real shadow と
normalized completion 5-branch / flat-rise law が同時に成立する。
-/
theorem exists_futureMinimum_shadow_and_normalizedCompletionBranch_after_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (start : ℕ) :
    ∃ L : ℝ,
      0 < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
        start < n ∧
        O.FutureMinimumAt n ∧
        O.exponent n = 1 ∧
        O.endpointCompletionStart SInf hn =
          O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
        O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
          O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
        (((2 : ℝ) ^ Critical.criticalTwoDepth n *
              (O.endpointCompletionEnd SInf hn : ℝ)) /
            (3 : ℝ) ^ n =
          O.normalizedEscapeCoordinate n +
            (2 : ℝ) ^ infinitePrefixDepth O.exponent n * (t : ℝ)) ∧
        0 < -O.normalizedEscapeShadowValue L n ∧
        (let δ := infiniteSurvivorDefect O.exponent n
         let qn :=
           ((endpointCompletionLiftStep O n t u : ℤ) : ℝ) /
             (2 : ℝ) ^ δ
         let rho := normalizedCompletionCocycleResidue n δ
         qn = rho - 4 ∨
           qn = rho ∨
           qn = rho + 4 ∨
           qn = rho + 8 ∨
           qn = rho + 12) ∧
        ((infiniteSurvivorDefect O.exponent (n + 1) =
              infiniteSurvivorDefect O.exponent n ∧
            ((endpointCompletionLiftStep O n t u : ℤ) : ℝ) /
                (2 : ℝ) ^ infiniteSurvivorDefect O.exponent n =
              2 * O.normalizedCompletionLiftCoefficient (n + 1) u -
                O.normalizedCompletionLiftCoefficient n t) ∨
          (infiniteSurvivorDefect O.exponent (n + 1) =
              infiniteSurvivorDefect O.exponent n + 1 ∧
            ((endpointCompletionLiftStep O n t u : ℤ) : ℝ) /
                (2 : ℝ) ^ infiniteSurvivorDefect O.exponent n =
              4 * O.normalizedCompletionLiftCoefficient (n + 1) u -
                O.normalizedCompletionLiftCoefficient n t)) := by
  rcases O.exists_normalizedEscapeLimit_of_linearDefect SInf hLinear with
    ⟨L, hL, hT, _hUpper⟩
  rcases O.exists_futureMinimum_consecutiveCompletionNatLifts_after SInf start with
    ⟨n, hn, t, u,
      hStart, hMin, _hOne, he,
      hStartT, _htPos, _htOdd, htBound, _hEndT,
      hStartU, _huPos, _huOdd, huBound, _hEndU⟩
  have hEndpointNorm :=
    O.endpointCompletion_normalized_eq_escape_add_lift SInf hn hStartT
  have hGap := O.normalizedEscapeShadowGap_pos_of_tendsto hT n
  have hFive :=
    O.endpointCompletionLiftStep_normalized_five_candidates_defect_of_exponent_eq_one
      SInf hn he hStartT hStartU htBound huBound
  have hBranch :=
    O.normalizedCompletionLiftStep_flat_or_rise
      SInf (t := t) (u := u) he
  exact
    ⟨L, hL, hT,
      n, hn, t, u,
      hStart, hMin, he,
      hStartT, hStartU,
      hEndpointNorm, hGap, hFive, hBranch⟩

end OddOrbit
end Collatz3
