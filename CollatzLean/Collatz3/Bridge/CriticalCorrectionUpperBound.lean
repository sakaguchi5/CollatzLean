import CollatzLean.Collatz3.Bridge.CriticalCorrectionLowerBound

/-!
# Collatz3 Bridge: high-orbit correction budget と critical margin

前段の necessary lower bound

`criticalMargin ≤ logCorrectionSum`

と既存の high-orbit upper bound

`logCorrectionSum ≤ oddSteps / (3 X ln 2)`

を合成する。

従って、全 odd-step start が `X` 以上の critical first-passage が
始点以上へ戻るには

`criticalMargin ≤ oddSteps / (3 X ln 2)`

が必要になる。
-/

namespace Collatz3
namespace Runs

/--
critical first-passage + endpoint nondecrease + high-orbit 条件から得る一般 budget inequality。
-/
theorem criticalMargin_le_steps_div_three_mul_log_two
    {X : ℕ}
    {w : Word}
    {x y : ℕ}
    (hFirst : ActualFirstPassage w x y)
    (hxy : x ≤ y)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x) :
    Bridge.criticalMargin (Word.oddSteps w) ≤
      (Word.oddSteps w : ℝ) /
        (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  have hLower :=
    criticalMargin_le_logCorrectionSum_of_actualFirstPassage
      hFirst hxy
  have hUpper :=
    hFirst.run.logCorrectionSum_le_steps_div_three_mul_log_two
      hX hAbove
  exact le_trans hLower hUpper

end Runs

namespace ActualSuffixMinimumCoefficientWindow

/--
window 自身の始点 `x` を lower height として使った定量形。

`μ(m) ≤ m / (3 x ln 2)`。
-/
theorem criticalMargin_le_steps_div_start
    {w : Word}
    {x y : ℕ}
    (h : ActualSuffixMinimumCoefficientWindow w x y) :
    Bridge.criticalMargin (Word.oddSteps w) ≤
      (Word.oddSteps w : ℝ) /
        (((3 : ℝ) * (x : ℝ)) * Real.log 2) := by
  exact
    Runs.criticalMargin_le_steps_div_three_mul_log_two
      h.actualFirstPassage h.endpoint_ge h.start_pos h.allStartsAtLeast

end ActualSuffixMinimumCoefficientWindow
end Collatz3
