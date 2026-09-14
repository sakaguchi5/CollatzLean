import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumBarrier
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Bridge.CriticalMargin
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Bridge: `(1,1)` future-minimum block の actual correction budget

`(carry, excess)=(1,1)` block `i → j`、長さ `r=j-i` では excess `1` だけから
whole segment の total two-depth が exact に

`criticalTwoDepth(r) = beattyIndex(r)+1`

になる。

finite actual run の log telescope と組み合わせると

`correctionSum = criticalMargin(r) + (log₂ y - log₂ x)`

が exact に従う。future minimum では block 内の全 step start が `x=value i` 以上なので、
既存の一様 correction upper bound を直接適用できる。

その結果 `(1,1)` には

`criticalMargin(r) < r / (3 x ln 2)`

が必要になる。

さらに future-minimum gap `y-x ≥ 4` を捨てずに使うと

`criticalMargin(r) + log₂(1 + 4/x) ≤ r / (3 x ln 2)`

という sharpened budget が得られる。

`CoefficientFirstPassage` packet は経由せず、`Runs` と local future-minimum semantics だけで閉じる。
-/

namespace Collatz3
namespace Runs

/--
total two-depth が exact critical depth なら、finite actual run の correction residual は

`criticalMargin(n) + (log₂ y - log₂ x)`

に exact に一致する。ここで `n=oddSteps(w)`。
-/
theorem logCorrectionSum_eq_criticalMargin_add_logGap_of_criticalDepth
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hDepth :
      Word.twoSteps w =
        Critical.criticalTwoDepth (Word.oddSteps w)) :
    h.logCorrectionSum =
      Bridge.criticalMargin (Word.oddSteps w) +
        (Real.logb 2 (y : ℝ) - Real.logb 2 (x : ℝ)) := by
  have hTel :=
    h.logb_end_eq_start_add_steps_sub_depth_add_correctionSum
  rw [hDepth] at hTel
  unfold Bridge.criticalMargin
  linarith

/--
critical depth の actual run で endpoint が strict に大きければ、
critical margin は correction sum より strict に小さい。
-/
theorem criticalMargin_lt_logCorrectionSum_of_criticalDepth_of_lt
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hDepth :
      Word.twoSteps w =
        Critical.criticalTwoDepth (Word.oddSteps w))
    (hxy : x < y) :
    Bridge.criticalMargin (Word.oddSteps w) <
      h.logCorrectionSum := by
  have hx : 0 < x := by
    have hStart := h.start_odd_of_nonempty (by
      intro hw
      rw [hw] at hDepth
      simp [Critical.criticalTwoDepth] at hDepth)
    rcases hStart with ⟨q, hq⟩
    omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hxyR : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hLog :
      Real.logb 2 (x : ℝ) < Real.logb 2 (y : ℝ) := by
    exact
      Real.logb_lt_logb
        (b := (2 : ℝ))
        (by norm_num)
        hxR hxyR
  have hExact :=
    h.logCorrectionSum_eq_criticalMargin_add_logGap_of_criticalDepth hDepth
  linarith

end Runs

namespace OddOrbit

open Bridge

/--
future minimum から始まる actual segment では、各 step start は開始値以上。

`Runs.AllStartsAtLeast` の arbitrary prefix endpoint は、同じ始点・同じ odd-step 数の
actual orbit segment と run 決定性で一致させる。
-/
theorem FutureMinimumAt.segment_allStartsAtLeast
    {O : Collatz3.OddOrbit}
    {i : ℕ}
    (hMin : O.FutureMinimumAt i)
    (r : ℕ) :
    Runs.AllStartsAtLeast
      (O.value i)
      (O.segmentWord i r)
      (O.value i) := by
  intro u v e a _hw hu
  let q : ℕ := Word.oddSteps u
  have hActual := O.runsSegment i q
  have hSame :=
    Runs.word_end_eq_of_common_start_same_oddSteps
      hu hActual (by simp [q])
  have hEnd : a = O.value (i + q) := hSame.2
  rw [hEnd]
  exact hMin (i + q) (by omega)

/--
`(carry, excess)=(1,1)` next-future-minimum block の total two-depth は exact critical depth。

この equality 自体には carry `1` は不要で、excess `1` が本質。
-/
theorem nextFutureMinimum_one_one_twoSteps_eq_criticalTwoDepth
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    Word.twoSteps (O.segmentWord i (j - i)) =
      Critical.criticalTwoDepth (j - i) := by
  have hDepth :=
    O.nextFutureMinimum_beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
      hNext
  rw [hOneOne.2] at hDepth
  unfold Critical.criticalTwoDepth
  omega

/--
`(1,1)` block の基本 actual correction budget。

`x=value i`, `r=j-i` とすると

`criticalMargin(r) < r / (3 x ln 2)`。
-/
theorem nextFutureMinimum_one_one_criticalMargin_lt_budget
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    criticalMargin (j - i) <
      ((j - i : ℕ) : ℝ) /
        (((3 : ℝ) * (O.value i : ℝ)) * Real.log 2) := by
  let r : ℕ := j - i
  have hIndex : i + r = j := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hRun :
      Runs (O.segmentWord i r) (O.value i) (O.value j) := by
    simpa [hIndex] using O.runsSegment i r
  have hDepth :
      Word.twoSteps (O.segmentWord i r) =
        Critical.criticalTwoDepth r := by
    simpa [r] using
      O.nextFutureMinimum_one_one_twoSteps_eq_criticalTwoDepth hNext hOneOne
  have hFour : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hLt : O.value i < O.value j := by omega
  have hLower :=
    hRun.criticalMargin_lt_logCorrectionSum_of_criticalDepth_of_lt
      (by simpa using hDepth) hLt
  have hx : 0 < O.value i := by
    have hOne := O.one_le_value i
    omega
  have hAbove :
      Runs.AllStartsAtLeast
        (O.value i) (O.segmentWord i r) (O.value i) :=
    hMin.segment_allStartsAtLeast r
  have hUpper :=
    hRun.logCorrectionSum_le_steps_div_three_mul_log_two
      hx hAbove
  have hBound := lt_of_lt_of_le hLower hUpper
  simpa [r] using hBound

/--
`(1,1)` block の gap-4 sharpened correction budget。

future-minimum gap `y-x ≥ 4` から

`log₂ y - log₂ x ≥ log₂(1+4/x)`

を exact に使い、

`criticalMargin(r) + log₂(1+4/x) ≤ r/(3x ln2)`

を得る。
-/
theorem nextFutureMinimum_one_one_gap_four_budget
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    criticalMargin (j - i) +
        Real.logb 2
          (1 + 4 / (O.value i : ℝ)) ≤
      ((j - i : ℕ) : ℝ) /
        (((3 : ℝ) * (O.value i : ℝ)) * Real.log 2) := by
  let r : ℕ := j - i
  have hIndex : i + r = j := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hRun :
      Runs (O.segmentWord i r) (O.value i) (O.value j) := by
    simpa [hIndex] using O.runsSegment i r
  have hDepth :
      Word.twoSteps (O.segmentWord i r) =
        Critical.criticalTwoDepth r := by
    simpa [r] using
      O.nextFutureMinimum_one_one_twoSteps_eq_criticalTwoDepth hNext hOneOne
  have hExact :=
    hRun.logCorrectionSum_eq_criticalMargin_add_logGap_of_criticalDepth
      (by simpa using hDepth)
  have hx : 0 < O.value i := by
    have hOne := O.one_le_value i
    omega
  have hy : 0 < O.value j := by
    have hOne := O.one_le_value j
    omega
  have hxR : (0 : ℝ) < (O.value i : ℝ) := by exact_mod_cast hx
  have hyR : (0 : ℝ) < (O.value j : ℝ) := by exact_mod_cast hy
  have hFour : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hGapNat : O.value i + 4 ≤ O.value j := by omega
  have hGapR : (O.value i : ℝ) + 4 ≤ (O.value j : ℝ) := by
    exact_mod_cast hGapNat
  have hArgPos :
      (0 : ℝ) < 1 + 4 / (O.value i : ℝ) := by
    positivity
  have hRatioLe :
      1 + 4 / (O.value i : ℝ) ≤
        (O.value j : ℝ) / (O.value i : ℝ) := by
    apply (le_div_iff₀ hxR).2
    calc
      (1 + 4 / (O.value i : ℝ)) * (O.value i : ℝ) =
          (O.value i : ℝ) + 4 := by
        field_simp [hxR.ne']
      _ ≤ (O.value j : ℝ) := hGapR
  have hLogRatio :
      Real.logb 2 (1 + 4 / (O.value i : ℝ)) ≤
        Real.logb 2 ((O.value j : ℝ) / (O.value i : ℝ)) := by
    exact
      Real.logb_le_logb_of_le
        (b := (2 : ℝ))
        (by norm_num)
        hArgPos hRatioLe
  have hLogGap :
      Real.logb 2 (1 + 4 / (O.value i : ℝ)) ≤
        Real.logb 2 (O.value j : ℝ) -
          Real.logb 2 (O.value i : ℝ) := by
    rw [Real.logb_div (b := (2 : ℝ)) hyR.ne' hxR.ne'] at hLogRatio
    exact hLogRatio
  have hOdd :
      Word.oddSteps (O.segmentWord i r) = r := by
    exact O.segmentWord_oddSteps i r
  have hExact' :
      hRun.logCorrectionSum =
        criticalMargin r +
          (Real.logb 2 (O.value j : ℝ) -
            Real.logb 2 (O.value i : ℝ)) := by
    simpa [hOdd] using hExact
  have hLower :
      criticalMargin r +
          Real.logb 2 (1 + 4 / (O.value i : ℝ)) ≤
        hRun.logCorrectionSum := by
    rw [hExact']
    exact add_le_add_right hLogGap (criticalMargin r)
  have hAbove :
      Runs.AllStartsAtLeast
        (O.value i) (O.segmentWord i r) (O.value i) :=
    hMin.segment_allStartsAtLeast r
  have hUpper :=
    hRun.logCorrectionSum_le_steps_div_three_mul_log_two
      hx hAbove
  have hBound := le_trans hLower hUpper
  simpa [r] using hBound

end OddOrbit
end Collatz3
