import CollatzLean.Collatz3.Bridge.CriticalMargin
import CollatzLean.Collatz3.Bridge.CoefficientFirstPassage
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Bridge: critical margin に必要な actual correction の下界

finite critical first-passage の exact log telescope を `criticalMargin` で書き直す。

endpoint が始点以上なら、pure terminal contraction

`criticalMargin(oddSteps w)`

を actual `+1` correction 総和が少なくとも埋めなければならない。

`Σ correction ≥ criticalMargin`

という必要条件を既存 `ActualFirstPassage` 上で証明し、
finite suffix-minimum coefficient window へ特殊化する。
-/

namespace Collatz3
namespace Runs

/--
actual critical first-passage が始点以上へ戻るなら、correction 総和は
terminal critical margin 以上である。
-/
theorem criticalMargin_le_logCorrectionSum_of_actualFirstPassage
    {w : Word}
    {x y : ℕ}
    (hFirst : ActualFirstPassage w x y)
    (hxy : x ≤ y) :
    Bridge.criticalMargin (Word.oddSteps w) ≤
      hFirst.run.logCorrectionSum := by
  have hx : 0 < x :=
    hFirst.run.start_pos_of_nonempty hFirst.word_nonempty
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxR : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast hx
  have hyR : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast hy
  have hxyR : (x : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hxy
  have hLog :
      Real.logb 2 (x : ℝ) ≤ Real.logb 2 (y : ℝ) := by
    exact
      (Real.logb_le_logb
        (b := (2 : ℝ))
        (by norm_num)
        hxR hyR).2 hxyR
  have hTel :=
    hFirst.run.logb_end_eq_start_add_steps_sub_depth_add_correctionSum
  have hDepth := hFirst.critical.totalTwoDepth_eq
  rw [hDepth] at hTel
  unfold Bridge.criticalMargin
  linarith

end Runs

namespace ActualSuffixMinimumCoefficientWindow

/--
finite suffix-minimum coefficient window では、actual correction 総和が
critical terminal margin を食い切る必要がある。
-/
theorem criticalMargin_le_logCorrectionSum
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    Bridge.criticalMargin (Word.oddSteps w) ≤
      h.run.logCorrectionSum := by
  exact
    Runs.criticalMargin_le_logCorrectionSum_of_actualFirstPassage
      h.actualFirstPassage h.endpoint_ge

end ActualSuffixMinimumCoefficientWindow
end Collatz3
