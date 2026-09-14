import CollatzLean.Collatz3.Bridge.InfiniteSurvivorOrbitBridge
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumCorrection
import CollatzLean.Collatz3.Bridge.CriticalMargin
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: survivor defect と actual log growth の exact bridge

無限 coefficient survivor の actual segment `i → i+r` について、

* global prefix depth,
* Beatty roof defect,
* critical margin,
* finite actual run の log correction sum

を同じ式へ戻す。

中心となる exact identity は

`log₂(y/x) = (δ_end - δ_start) + μ(start) - μ(end) + correctionSum`。

ここで defect 差は `ℝ` 上の signed difference として書く。
従ってこの定理自体には Global CST も future-minimum 仮定も不要である。

さらに correction sum の非負性と `0 < μ ≤ 1` だけから

`defectGap - 1 < log₂(y/x)`

が従う。future minimum を始点にした場合には、区間内の全 step start が開始値以上なので、
既存の一様 correction budget を使って逆向きの upper bound も得る。

新しい orbit data / packet は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
無限 coefficient survivor の任意 actual segment に対する exact defect--log bridge。

`δ_m = beattyIndex(m) - prefixDepth(m)` と
`μ(m) = beattyIndex(m) + 1 - m log₂3` を finite run の log telescope に代入すると

`log₂(value(i+r)) - log₂(value(i))`
`= δ_(i+r) - δ_i + μ(i) - μ(i+r) + correctionSum`

となる。
-/
theorem survivorSegment_logValueGap_eq_defectGap_add_marginGap_add_correctionSum
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (i r : ℕ) :
    Real.logb 2 (O.value (i + r) : ℝ) -
        Real.logb 2 (O.value i : ℝ) =
      ((infiniteSurvivorDefect O.exponent (i + r) : ℕ) : ℝ) -
        ((infiniteSurvivorDefect O.exponent i : ℕ) : ℝ) +
        criticalMargin i - criticalMargin (i + r) +
        (O.runsSegment i r).logCorrectionSum := by
  have hRun :=
    (O.runsSegment i r).logb_end_eq_start_add_steps_sub_depth_add_correctionSum
  have hOdd : Word.oddSteps (O.segmentWord i r) = r :=
    O.segmentWord_oddSteps i r
  rw [hOdd] at hRun
  have hDepth := O.infinitePrefixDepth_add_eq i r
  have hStart := beattyIndex_eq_prefixDepth_add_defect S i
  have hEnd := beattyIndex_eq_prefixDepth_add_defect S (i + r)
  have hBalance :
      Word.twoSteps (O.segmentWord i r) +
          infiniteSurvivorDefect O.exponent (i + r) +
          Critical.beattyIndex i =
        Critical.beattyIndex (i + r) +
          infiniteSurvivorDefect O.exponent i := by
    omega
  have hBalanceR :
      (Word.twoSteps (O.segmentWord i r) : ℝ) +
          (infiniteSurvivorDefect O.exponent (i + r) : ℝ) +
          (Critical.beattyIndex i : ℝ) =
        (Critical.beattyIndex (i + r) : ℝ) +
          (infiniteSurvivorDefect O.exponent i : ℝ) := by
    exact_mod_cast hBalance
  rw [
    criticalMargin_eq_beattyIndex_add_one_sub i,
    criticalMargin_eq_beattyIndex_add_one_sub (i + r)
  ]
  push_cast
  nlinarith [hRun, hBalanceR]

/--
前定理と correction sum の非負性、`0 < μ(start)`、`μ(end) ≤ 1` だけを使う universal lower bound。

signed defect gap が大きければ actual `log₂` value gap も同じだけ大きくなり、
endpoint margin による損失は strict に `1` 未満である。
-/
theorem survivorSegment_defectGap_sub_one_lt_logValueGap
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (i r : ℕ) :
    ((infiniteSurvivorDefect O.exponent (i + r) : ℕ) : ℝ) -
        ((infiniteSurvivorDefect O.exponent i : ℕ) : ℝ) - 1 <
      Real.logb 2 (O.value (i + r) : ℝ) -
        Real.logb 2 (O.value i : ℝ) := by
  have hExact :=
    O.survivorSegment_logValueGap_eq_defectGap_add_marginGap_add_correctionSum
      S i r
  have hCorr :
      0 ≤ (O.runsSegment i r).logCorrectionSum :=
    (O.runsSegment i r).logCorrectionSum_nonneg
  have hStart := criticalMargin_pos i
  have hEnd := criticalMargin_le_one (i + r)
  linarith

/--
defect が segment 上で非減少なら、signed defect gap を自然数差へ戻した形。

後段の Global CST / future-minimum counting から直接使うための wrapper。
-/
theorem survivorSegment_natDefectGrowth_sub_one_lt_logValueGap
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (i r : ℕ)
    (hNondec :
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent (i + r)) :
    (((infiniteSurvivorDefect O.exponent (i + r) -
          infiniteSurvivorDefect O.exponent i : ℕ) : ℝ) - 1) <
      Real.logb 2 (O.value (i + r) : ℝ) -
        Real.logb 2 (O.value i : ℝ) := by
  rw [Nat.cast_sub hNondec]
  exact O.survivorSegment_defectGap_sub_one_lt_logValueGap S i r

/--
future minimum を始点にした segment では correction sum に actual-value budget を入れられる。

exact bridge と

`correctionSum ≤ r / (3 * value(i) * ln 2)`

をそのまま合成した upper bound。
-/
theorem FutureMinimumAt.survivorSegment_logValueGap_le_defectMargin_add_budget
    {O : Collatz3.OddOrbit}
    {i : ℕ}
    (hMin : O.FutureMinimumAt i)
    (S : O.IsInfiniteCoefficientSurvivor)
    (r : ℕ) :
    Real.logb 2 (O.value (i + r) : ℝ) -
        Real.logb 2 (O.value i : ℝ) ≤
      ((infiniteSurvivorDefect O.exponent (i + r) : ℕ) : ℝ) -
        ((infiniteSurvivorDefect O.exponent i : ℕ) : ℝ) +
        criticalMargin i - criticalMargin (i + r) +
        (r : ℝ) /
          (((3 : ℝ) * (O.value i : ℝ)) * Real.log 2) := by
  have hExact :=
    O.survivorSegment_logValueGap_eq_defectGap_add_marginGap_add_correctionSum
      S i r
  have hx : 0 < O.value i := by
    have hOne := O.one_le_value i
    omega
  have hAbove :
      Runs.AllStartsAtLeast
        (O.value i) (O.segmentWord i r) (O.value i) :=
    hMin.segment_allStartsAtLeast r
  have hUpper :=
    (O.runsSegment i r).logCorrectionSum_le_steps_div_three_mul_log_two
      hx hAbove
  have hOdd : Word.oddSteps (O.segmentWord i r) = r :=
    O.segmentWord_oddSteps i r
  rw [hOdd] at hUpper
  linarith

end OddOrbit
end Collatz3
