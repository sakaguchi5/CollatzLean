import CollatzLean.Collatz3.Bridge.InfiniteSurvivorOrbitBridge
import CollatzLean.Collatz3.Semantics.OrbitDerived
import CollatzLean.Collatz3.Semantics.OrbitFateClassical
import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Collatz3 Bridge: actual infinite coefficient survivor は +∞ へ逃げる

actual `OddOrbit` が coefficient survivor であり続けると仮定する。

まず任意の nonempty prefix では

`2^D ≤ 3^m`

で、actual affine translation は正なので endpoint は initial value より strict に大きい。
従って `1` には到達できない。

さらに非自明 repeat が存在すると、その return period `d` の two-depth `H` は
actual return equation から

`3^d < 2^H`

を満たす。同じ period を十分多く反復すれば、この strict contraction が任意の有限 transient
coefficient を上回り、global survivor inequality と矛盾する。

よって hit 1 も repeat も無く、既存の classical coverage theorem から軌道は
`DivergesToInfinity`。その結果、既存 future-minimum 理論により任意に遠く
`exponent = 1` の actual future minimum anchor が存在する。
-/

namespace Collatz3
namespace Bridge

open Filter

/-- 非空 exponent word の affine translation は正。 -/
theorem affineConst_pos_of_nonempty
    {w : Word}
    (hne : w ≠ []) :
    0 < Word.affineConst w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      rw [Word.affineConst_cons]
      exact Nat.add_pos_left (Nat.pow_pos (by decide : 0 < (3 : ℕ))) _

/--
`0 < B < A` なら、任意の有限係数 `C` は十分大きい冪で
`C * B^k < A^k` に吸収される。
-/
theorem exists_mul_pow_lt_pow_of_lt
    {A B C : ℕ}
    (hB : 0 < B)
    (hBA : B < A) :
    ∃ k : ℕ, C * B ^ k < A ^ k := by
  let r : ℝ := (A : ℝ) / (B : ℝ)
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hBAR : (B : ℝ) < (A : ℝ) := by exact_mod_cast hBA
  have hr : (1 : ℝ) < r := by
    dsimp [r]
    exact (one_lt_div₀ hBR).2 hBAR
  have hT : Tendsto (fun k : ℕ => r ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  have hEventually : ∀ᶠ k : ℕ in atTop, (C : ℝ) < r ^ k :=
    hT.eventually_gt_atTop (C : ℝ)
  obtain ⟨K, hMain⟩ := hEventually.exists
  refine ⟨K, ?_⟩
  have hPowB : (0 : ℝ) < (B : ℝ) ^ K := pow_pos hBR K
  have hDiv :
      (C : ℝ) * (B : ℝ) ^ K < (A : ℝ) ^ K := by
    have hMain' :
        (C : ℝ) < (A : ℝ) ^ K / (B : ℝ) ^ K := by
      simpa [r, div_pow] using hMain
    exact (lt_div_iff₀ hPowB).1 hMain'
  exact_mod_cast hDiv

end Bridge

namespace OddOrbit

open Bridge

/-- infinite coefficient survivor の任意 nonempty initial segment は始点より上で終わる。 -/
theorem start_lt_value_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    O.value 0 < O.value m := by
  let w := O.segmentWord 0 m
  have hne : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps 0 m
    change Word.oddSteps w = m at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hRun : Runs w (O.value 0) (O.value m) := by
    simpa [w] using O.runsSegment 0 m
  have hEq := (Word.endpointEquation_iff w (O.value 0) (O.value m)).1 hRun.endpointEquation
  have hA : 0 < Word.affineConst w := affineConst_pos_of_nonempty hne
  have hDepth :
      Word.twoSteps w = infinitePrefixDepth O.exponent m := by
    simpa [w] using O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m
  have hOdd : Word.oddSteps w = m := by
    simp only [segmentWord_oddSteps, w]
  have hCoeffDepth := S.prefixDepth_le_beatty m
  have hPowLeRoof :
      2 ^ infinitePrefixDepth O.exponent m ≤
        2 ^ Critical.beattyIndex m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hCoeffDepth
  have hCoeff :
      2 ^ Word.twoSteps w ≤ 3 ^ Word.oddSteps w := by
    rw [hDepth, hOdd]
    exact le_trans hPowLeRoof (Critical.beattyIndex_lower m)
  have hLeft :
      2 ^ Word.twoSteps w * O.value 0 ≤
        3 ^ Word.oddSteps w * O.value 0 :=
    Nat.mul_le_mul_right (O.value 0) hCoeff
  have hStrictTranslate :
      3 ^ Word.oddSteps w * O.value 0 <
        3 ^ Word.oddSteps w * O.value 0 + Word.affineConst w :=
    Nat.lt_add_of_pos_right hA
  have hMul :
      2 ^ Word.twoSteps w * O.value 0 <
        2 ^ Word.twoSteps w * O.value m := by
    calc
      2 ^ Word.twoSteps w * O.value 0
          ≤ 3 ^ Word.oddSteps w * O.value 0 := hLeft
      _ < 3 ^ Word.oddSteps w * O.value 0 + Word.affineConst w :=
        hStrictTranslate
      _ = 2 ^ Word.twoSteps w * O.value m := hEq.symm
  exact
    (Nat.mul_lt_mul_left (Arithmetic.twoPow_pos (Word.twoSteps w))).mp hMul

/-- infinite coefficient survivor は `1` に到達しない。 -/
theorem no_hitsOne_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor) :
    ¬ O.HitsOne := by
  rintro ⟨n, hn⟩
  cases n with
  | zero =>
      have hNext := O.start_lt_value_of_infiniteCoefficientSurvivor S (m := 1) (by omega)
      have hOneNext := O.value_eq_one_add_of_value_eq_one hn 1
      simp only [Nat.zero_add] at hOneNext
      rw [hn, hOneNext] at hNext
      omega
  | succ n =>
      have hRise :=
        O.start_lt_value_of_infiniteCoefficientSurvivor S
          (m := n + 1) (by omega)
      have hStartOne : 1 ≤ O.value 0 := O.one_le_value 0
      rw [hn] at hRise
      omega

/-- repeated base から任意の period multiple にある segment word は同じ period word。 -/
theorem segmentWord_mul_period_eq_of_repeat
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j)
    (k q : ℕ) :
    O.segmentWord (i + k * (j - i)) q = O.segmentWord i q := by
  have hValue := O.value_eq_repeat_base_mul_period hij heq k
  have hRunK := O.runsSegment (i + k * (j - i)) q
  have hRun0 := O.runsSegment i q
  rw [hValue] at hRunK
  exact
    (Runs.word_end_eq_of_common_start_same_oddSteps
      hRunK hRun0 (by simp)).1

/-- repeated period `k` 回分の total two-depth は `k * H`。 -/
theorem twoSteps_segmentWord_mul_period_of_repeat
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j)
    (k : ℕ) :
    Word.twoSteps (O.segmentWord i (k * (j - i))) =
      k * Word.twoSteps (O.segmentWord i (j - i)) := by
  let d := j - i
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hAdd := O.segmentWord_add i (k * d) d
      have hPeriod :=
        O.segmentWord_mul_period_eq_of_repeat hij heq k d
      have hIndex : (k + 1) * d = k * d + d := by ring
      rw [hIndex, hAdd, Word.twoSteps_append, hPeriod, ih]
      ring

/-- global prefix depth は repeated period に沿って affine に増える。 -/
theorem infinitePrefixDepth_repeat_mul
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j)
    (k : ℕ) :
    infinitePrefixDepth O.exponent (i + k * (j - i)) =
      infinitePrefixDepth O.exponent i +
        k * Word.twoSteps (O.segmentWord i (j - i)) := by
  rw [O.infinitePrefixDepth_add_eq i (k * (j - i))]
  rw [O.twoSteps_segmentWord_mul_period_of_repeat hij heq k]

/-- nonempty actual return period は coefficient として strict contraction。 -/
theorem threePow_lt_twoPow_period_of_repeat
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    3 ^ (j - i) <
      2 ^ Word.twoSteps (O.segmentWord i (j - i)) := by
  let d := j - i
  let w := O.segmentWord i d
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hReturn := O.returnsTo_segmentWord_of_repeat hij heq
  have hA : 0 < Word.affineConst w := by
    apply affineConst_pos_of_nonempty
    exact hReturn.word_nonempty
  have hEq :=
    (Word.endpointEquation_iff w (O.value i) (O.value i)).1
      hReturn.run.endpointEquation
  have hx : 0 < O.value i := by
    have hOne := O.one_le_value i
    omega
  have hProd :
      3 ^ Word.oddSteps w * O.value i <
        2 ^ Word.twoSteps w * O.value i := by
    calc
      3 ^ Word.oddSteps w * O.value i
          < 3 ^ Word.oddSteps w * O.value i + Word.affineConst w :=
        Nat.lt_add_of_pos_right hA
      _ = 2 ^ Word.twoSteps w * O.value i := hEq.symm
  have hCoeff : 3 ^ Word.oddSteps w < 2 ^ Word.twoSteps w :=
    (Nat.mul_lt_mul_right hx).mp hProd
  simpa [w, d] using hCoeff

/-- infinite coefficient survivor では非自明 repeat は不可能。 -/
theorem no_nontrivialRepeat_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor) :
    ¬ O.HasNontrivialRepeat := by
  rintro ⟨i, j, hij, heq, _hiOne⟩
  let d := j - i
  let H := Word.twoSteps (O.segmentWord i d)
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hContract : 3 ^ d < 2 ^ H := by
    simpa [d, H] using O.threePow_lt_twoPow_period_of_repeat hij heq
  obtain ⟨k, hk⟩ :=
    exists_mul_pow_lt_pow_of_lt
      (A := 2 ^ H) (B := 3 ^ d) (C := 3 ^ i)
      (Nat.pow_pos (by decide)) hContract
  let m := i + k * d
  have hDepth :
      infinitePrefixDepth O.exponent (i + k * d) =
        infinitePrefixDepth O.exponent i + k * H := by
    simpa [d, H] using O.infinitePrefixDepth_repeat_mul hij heq k
  have hSurvive := S.prefixDepth_le_beatty m
  have hPowDepthRoof :
      2 ^ infinitePrefixDepth O.exponent m ≤
        2 ^ Critical.beattyIndex m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hSurvive
  have hSurvivePow :
      2 ^ infinitePrefixDepth O.exponent m ≤ 3 ^ m :=
    le_trans hPowDepthRoof (Critical.beattyIndex_lower m)
  have hOnePow : 1 ≤ 2 ^ infinitePrefixDepth O.exponent i := by
    exact Nat.succ_le_iff.mpr (Arithmetic.twoPow_pos (infinitePrefixDepth O.exponent i))
  have hMulLe :
      (2 ^ H) ^ k ≤
        2 ^ infinitePrefixDepth O.exponent i * (2 ^ H) ^ k := by
    have := Nat.mul_le_mul_right ((2 ^ H) ^ k) hOnePow
    simpa [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hBadRaw :
      3 ^ i * (3 ^ d) ^ k <
        2 ^ infinitePrefixDepth O.exponent i * (2 ^ H) ^ k :=
    lt_of_lt_of_le hk hMulLe
  have hBad : 3 ^ m < 2 ^ infinitePrefixDepth O.exponent m := by
    calc
      3 ^ m = 3 ^ i * (3 ^ d) ^ k := by
        dsimp [m]
        rw [pow_add, Nat.mul_comm k d, pow_mul]
      _ < 2 ^ infinitePrefixDepth O.exponent i * (2 ^ H) ^ k := hBadRaw
      _ = 2 ^ (infinitePrefixDepth O.exponent i + k * H) := by
        rw [pow_add, Nat.mul_comm k H, pow_mul]
      _ = 2 ^ infinitePrefixDepth O.exponent m := by
        rw [hDepth]
  exact (not_lt_of_ge hSurvivePow) hBad

/-- actual infinite coefficient survivor は必ず `+∞` へ発散する。 -/
theorem divergesToInfinity_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor) :
    O.DivergesToInfinity := by
  exact
    O.divergesToInfinity_of_no_hit_no_repeat
      (O.no_hitsOne_of_infiniteCoefficientSurvivor S)
      (O.no_nontrivialRepeat_of_infiniteCoefficientSurvivor S)

/-- survivor orbit では任意に遠く actual future minimum が存在する。 -/
theorem exists_futureMinimum_one_lt_after_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n := by
  exact
    O.exists_futureMinimum_one_lt_after_of_diverges
      (O.divergesToInfinity_of_infiniteCoefficientSurvivor S) start

/--
survivor orbit では任意に遠い future-minimum anchor で exponent が exact に `1`。
-/
theorem exists_futureMinimum_exponent_eq_one_after_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 := by
  exact
    O.exists_futureMinimum_exponent_eq_one_after_of_diverges
      (O.divergesToInfinity_of_infiniteCoefficientSurvivor S) start

end OddOrbit
end Collatz3
