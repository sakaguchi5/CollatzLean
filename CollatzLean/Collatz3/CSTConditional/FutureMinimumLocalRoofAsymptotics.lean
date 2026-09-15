import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoof
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow
import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeightLemma41
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: local roof contribution の無限和・Cesàro・密度零

前段 `FutureMinimumLocalRoof` では、future minimum `i` から見た local row `r` に対して

`c_i(r) = criticalEscapeWeight r / 2^(futureMinimum_localRoofDefect O i r)`

を導入し、これは global normalized escape increment を開始点 `i` の scale へ戻したものと
exact に一致することを示した。

このファイルでは新しい primitive data を追加しない。
有限和の telescope と既存 normalized escape limit `R_m -> L` だけから

* local contribution の有限和は scaled escape gap、
* `Σ_r c_i(r) = -Z_i(L)`、
* local contribution の Cesàro 平均は `0`、
* Lemma 41 と引き算すると weighted roof deficit の平均は `1/(6 log 2)`、
* 任意の固定深さ `D` について `d_i(r) ≤ D` となる row の自然密度は `0`

を derived theorem として得る。

従って A 型で normalized escape limit が存在する場合、固定 future minimum から見た profile は
Sturmian roof に密度正で張り付くことはできない。
むしろ任意の固定 roof-depth band から density one で離れる必要がある。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter
open scoped Topology BigOperators Real

/--
local roof contribution の有限和は、同じ区間の normalized escape gap を
開始 future minimum の scale へ戻したものに exact に一致する。
-/
theorem futureMinimumLocalRoofContribution_sum_range_eq_scaledEscapeGap
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (N : ℕ) :
    (Finset.sum (Finset.range N) (fun r =>
        O.futureMinimumLocalRoofContribution start r)) =
      ((3 : ℝ) ^ start /
          (2 : ℝ) ^ infinitePrefixDepth O.exponent start) *
        (O.normalizedEscapeCoordinate (start + N) -
          O.normalizedEscapeCoordinate start) := by
  let c : ℝ :=
    (3 : ℝ) ^ start /
      (2 : ℝ) ^ infinitePrefixDepth O.exponent start
  calc
    (Finset.sum (Finset.range N) (fun r =>
        O.futureMinimumLocalRoofContribution start r))
        = Finset.sum (Finset.range N) (fun r =>
            c * O.normalizedEscapeIncrement (start + r)) := by
              apply Finset.sum_congr rfl
              intro r _hr
              dsimp [c]
              exact
                (O.scaledEscapeIncrement_eq_criticalEscapeWeight_div_localRoofDefect
                  G hStart r).symm
    _ = c *
          (Finset.sum (Finset.range N) (fun r =>
            O.normalizedEscapeIncrement (start + r))) :=
          (Finset.mul_sum ..).symm
    _ = c *
          (O.normalizedEscapeCoordinate (start + N) -
            O.normalizedEscapeCoordinate start) := by
          have hTel :=
            O.normalizedEscapeCoordinate_add_eq_add_sum_range start N
          have hSum :
              (Finset.sum (Finset.range N) (fun r =>
                O.normalizedEscapeIncrement (start + r))) =
                O.normalizedEscapeCoordinate (start + N) -
                  O.normalizedEscapeCoordinate start := by
            linarith [hTel]
          rw [hSum]

/--
`R_m -> L` なら、future minimum `start` から見た local roof contribution の有限和は
その点の positive shadow gap `-Z_start(L)` へ収束する。
-/
theorem futureMinimumLocalRoofContribution_partialSum_tendsto_shadowGap
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun N : ℕ =>
        Finset.sum (Finset.range N) (fun r =>
          O.futureMinimumLocalRoofContribution start r))
      atTop
      (nhds (-O.normalizedEscapeShadowValue L start)) := by
  let c : ℝ :=
    (3 : ℝ) ^ start /
      (2 : ℝ) ^ infinitePrefixDepth O.exponent start
  have hShiftRaw :
      Tendsto
        (fun N : ℕ => O.normalizedEscapeCoordinate (N + start))
        atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat start).2 hT
  have hShift :
      Tendsto
        (fun N : ℕ => O.normalizedEscapeCoordinate (start + N))
        atTop (nhds L) := by
    simpa [Nat.add_comm] using hShiftRaw
  have hGap :
      Tendsto
        (fun N : ℕ =>
          O.normalizedEscapeCoordinate (start + N) -
            O.normalizedEscapeCoordinate start)
        atTop
        (nhds (L - O.normalizedEscapeCoordinate start)) :=
    hShift.sub_const (O.normalizedEscapeCoordinate start)
  have hScaled :
      Tendsto
        (fun N : ℕ =>
          c *
            (O.normalizedEscapeCoordinate (start + N) -
              O.normalizedEscapeCoordinate start))
        atTop
        (nhds (c * (L - O.normalizedEscapeCoordinate start))) :=
    tendsto_const_nhds.mul hGap
  have hFun :
      (fun N : ℕ =>
        Finset.sum (Finset.range N) (fun r =>
          O.futureMinimumLocalRoofContribution start r)) =
      (fun N : ℕ =>
        c *
          (O.normalizedEscapeCoordinate (start + N) -
            O.normalizedEscapeCoordinate start)) := by
    funext N
    dsimp [c]
    exact
      O.futureMinimumLocalRoofContribution_sum_range_eq_scaledEscapeGap
        G hStart N
  have hTarget :
      c * (L - O.normalizedEscapeCoordinate start) =
        -O.normalizedEscapeShadowValue L start := by
    rw [O.neg_normalizedEscapeShadowValue_eq_limitGap_scaled L start]
    dsimp [c]
    ring
  rw [hFun]
  simpa [hTarget] using hScaled

/--
local roof contribution は positive term series として shadow gap に exact に総和する。
-/
theorem hasSum_futureMinimumLocalRoofContribution_eq_shadowGap
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    HasSum
      (fun r : ℕ => O.futureMinimumLocalRoofContribution start r)
      (-O.normalizedEscapeShadowValue L start) := by
  apply
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun r => O.futureMinimumLocalRoofContribution_nonneg start r)
      (-O.normalizedEscapeShadowValue L start)).2
  exact
    O.futureMinimumLocalRoofContribution_partialSum_tendsto_shadowGap
      G hStart hT

/--
A 型 route で使う中心 `tsum` identity。

`-Z_i(L) = Σ_r criticalEscapeWeight(r) / 2^(d_i(r))`。

ここで `d_i(r)` は future minimum `i` から見た local roof defect。
-/
theorem shadowGap_eq_tsum_localCriticalEscapeWeight
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    -O.normalizedEscapeShadowValue L start =
      ∑' r : ℕ,
        criticalEscapeWeight r /
          (2 : ℝ) ^ O.futureMinimum_localRoofDefect start r := by
  have hHas :=
    O.hasSum_futureMinimumLocalRoofContribution_eq_shadowGap
      G hStart hT
  have hEq := hHas.tsum_eq
  unfold futureMinimumLocalRoofContribution at hEq
  exact hEq.symm

/--
local roof contribution の Cesàro 平均は `0` へ収束する。

理由は、その partial sum 自体が有限値 `-Z_start(L)` へ収束するため。
-/
theorem localRoofContribution_cesaro_tendsto_zero
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun N : ℕ =>
        (Finset.sum (Finset.range N) (fun r =>
          O.futureMinimumLocalRoofContribution start r)) / (N : ℝ))
      atTop
      (nhds 0) := by
  have hSum :=
    O.futureMinimumLocalRoofContribution_partialSum_tendsto_shadowGap
      G hStart hT
  have hInv :
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hMul := hSum.mul hInv
  simpa [div_eq_mul_inv] using hMul

/--
Lemma 41 の canonical roof weight から actual local contribution を引いた
weighted roof deficit の Cesàro 平均は exact に `1/(6 log 2)`。

`average(w_r) -> 1/(6 log 2)` と `average(c_i(r)) -> 0` の直接差。
-/
theorem weightedRoofDeficit_cesaro
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun N : ℕ =>
        (Finset.sum (Finset.range N) (fun r =>
          (criticalEscapeWeight r -
            O.futureMinimumLocalRoofContribution start r))) / (N : ℝ))
      atTop
      (nhds (1 / (6 * Real.log 2))) := by
  have hWeight := tendsto_criticalEscapeWeight_cesaro
  have hLocal :=
    O.localRoofContribution_cesaro_tendsto_zero G hStart hT
  have hDiff := hWeight.sub hLocal
  have hFun :
      (fun N : ℕ =>
        (Finset.sum (Finset.range N) (fun r =>
          (criticalEscapeWeight r -
            O.futureMinimumLocalRoofContribution start r))) / (N : ℝ)) =
      (fun N : ℕ =>
        (Finset.sum (Finset.range N) (fun r => criticalEscapeWeight r)) / (N : ℝ) -
          (Finset.sum (Finset.range N) (fun r =>
            O.futureMinimumLocalRoofContribution start r)) / (N : ℝ)) := by
    funext N
    rw [Finset.sum_sub_distrib]
    ring
  rw [hFun]
  simpa using hDiff

/--
local roof defect が固定深さ `D` 以下なら、その row contribution は
一様な正量 `1 / (6 * 2^D)` 以上。

ここでは Lemma 41 の平均値は使わず、pointwise bound `1/6 < w_r` だけを使う。
-/
theorem one_div_six_twoPow_le_localRoofContribution_of_defect_le
    (O : Collatz3.OddOrbit)
    (start r D : ℕ)
    (hDepth : O.futureMinimum_localRoofDefect start r ≤ D) :
    1 / (6 * (2 : ℝ) ^ D) ≤
      O.futureMinimumLocalRoofContribution start r := by
  let d : ℕ := O.futureMinimum_localRoofDefect start r
  have hPow : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ D := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by simpa [d] using hDepth)
  have hDen :
      6 * (2 : ℝ) ^ d ≤ 6 * (2 : ℝ) ^ D := by
    nlinarith
  have hRecip :
      1 / (6 * (2 : ℝ) ^ D) ≤
        1 / (6 * (2 : ℝ) ^ d) := by
    exact one_div_le_one_div_of_le (by positivity) hDen
  have hWeight := (criticalEscapeWeight_mem_Ioc_one_six_one_third r).1
  have hPowPos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hWeightDiv :
      ((1 : ℝ) / 6) / (2 : ℝ) ^ d ≤
        criticalEscapeWeight r / (2 : ℝ) ^ d :=
    (div_le_div_iff_of_pos_right hPowPos).2 hWeight.le
  calc
    1 / (6 * (2 : ℝ) ^ D)
        ≤ 1 / (6 * (2 : ℝ) ^ d) := hRecip
    _ = ((1 : ℝ) / 6) / (2 : ℝ) ^ d := by
          field_simp
    _ ≤ criticalEscapeWeight r / (2 : ℝ) ^ d := hWeightDiv
    _ = O.futureMinimumLocalRoofContribution start r := by
          simp [futureMinimumLocalRoofContribution, d]

/--
固定深さ `D` 以下の row 数は、local contribution の有限和で一様に支配される。

`# {r<N | d_i(r) ≤ D} ≤ 6*2^D * Σ_{r<N} c_i(r)`。
-/
theorem boundedLocalRoofDefect_count_le_scaledContributionSum
    (O : Collatz3.OddOrbit)
    (start D N : ℕ) :
    (((Finset.range N).filter
        (fun r => O.futureMinimum_localRoofDefect start r ≤ D)).card : ℝ) ≤
      (6 * (2 : ℝ) ^ D) *
        (Finset.sum (Finset.range N) (fun r =>
          O.futureMinimumLocalRoofContribution start r)) := by
  classical
  let C : ℝ := 6 * (2 : ℝ) ^ D
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hTerm :
      ∀ r ∈ Finset.range N,
        (if O.futureMinimum_localRoofDefect start r ≤ D then (1 : ℝ) else 0) ≤
          C * O.futureMinimumLocalRoofContribution start r := by
    intro r _hr
    by_cases hDepth : O.futureMinimum_localRoofDefect start r ≤ D
    · simp only [hDepth, ite_true]
      have hLower :=
        O.one_div_six_twoPow_le_localRoofContribution_of_defect_le
          start r D hDepth
      have hLower' :
          1 / C ≤ O.futureMinimumLocalRoofContribution start r := by
        simpa [C] using hLower
      have hMul := (div_le_iff₀ hCPos).1 hLower'
      simpa [mul_comm] using hMul
    · simp only [hDepth, ite_false]
      exact mul_nonneg hCPos.le
        (O.futureMinimumLocalRoofContribution_nonneg start r)
  calc
    (((Finset.range N).filter
        (fun r => O.futureMinimum_localRoofDefect start r ≤ D)).card : ℝ)
        = Finset.sum
            ((Finset.range N).filter
              (fun r => O.futureMinimum_localRoofDefect start r ≤ D))
            (fun _r => (1 : ℝ)) := by simp
    _ = Finset.sum (Finset.range N) (fun r =>
          if O.futureMinimum_localRoofDefect start r ≤ D then (1 : ℝ) else 0) := by
          rw [Finset.sum_filter]
    _ ≤ Finset.sum (Finset.range N) (fun r =>
          C * O.futureMinimumLocalRoofContribution start r) := by
          apply Finset.sum_le_sum
          intro r hr
          exact hTerm r hr
    _ = C *
          (Finset.sum (Finset.range N) (fun r =>
            O.futureMinimumLocalRoofContribution start r)) :=
          (Finset.mul_sum ..).symm
    _ = (6 * (2 : ℝ) ^ D) *
          (Finset.sum (Finset.range N) (fun r =>
            O.futureMinimumLocalRoofContribution start r)) := by
          rfl

/--
固定深さ band の有限密度は、local contribution の Cesàro 平均の
`6*2^D` 倍以下。
-/
theorem boundedLocalRoofDefect_density_le_scaledContributionCesaro
    (O : Collatz3.OddOrbit)
    (start D N : ℕ) :
    (((Finset.range N).filter
        (fun r => O.futureMinimum_localRoofDefect start r ≤ D)).card : ℝ) /
        (N : ℝ) ≤
      (6 * (2 : ℝ) ^ D) *
        ((Finset.sum (Finset.range N) (fun r =>
          O.futureMinimumLocalRoofContribution start r)) / (N : ℝ)) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hNPosNat : 0 < N := Nat.pos_of_ne_zero hN
    have hNPos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast hNPosNat
    have hCount := O.boundedLocalRoofDefect_count_le_scaledContributionSum start D N
    apply (div_le_iff₀ hNPos).2
    calc
      (((Finset.range N).filter
          (fun r => O.futureMinimum_localRoofDefect start r ≤ D)).card : ℝ)
          ≤ (6 * (2 : ℝ) ^ D) *
              (Finset.sum (Finset.range N) (fun r =>
                O.futureMinimumLocalRoofContribution start r)) := hCount
      _ =
          ((6 * (2 : ℝ) ^ D) *
              ((Finset.sum (Finset.range N) (fun r =>
                O.futureMinimumLocalRoofContribution start r)) / (N : ℝ))) *
            (N : ℝ) := by
              field_simp [hNPos.ne']

/--
A 型 route の幾何的必要条件。

`R_m -> L` を持つ Global-CST future minimum `start` を固定すると、任意の固定 `D` について

`#{r<N | futureMinimum_localRoofDefect start r ≤ D} / N -> 0`。

つまり roof から固定距離以内に残る row の自然密度は必ず `0`。
これは「late shape が roof に固定される」のではなく、固定 anchor から見た profile が
任意の bounded roof band から density one で離れることを意味する。
-/
theorem boundedLocalRoofDefect_density_zero
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    (D : ℕ) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter
          (fun r => O.futureMinimum_localRoofDefect start r ≤ D)).card : ℝ) /
          (N : ℝ))
      atTop
      (nhds 0) := by
  let C : ℝ := 6 * (2 : ℝ) ^ D
  have hLocal :=
    O.localRoofContribution_cesaro_tendsto_zero G hStart hT
  have hUpper :
      Tendsto
        (fun N : ℕ =>
          C *
            ((Finset.sum (Finset.range N) (fun r =>
              O.futureMinimumLocalRoofContribution start r)) / (N : ℝ)))
        atTop
        (nhds 0) := by
    have hConst :
        Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa using hConst.mul hLocal
  apply
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hUpper
  · exact Eventually.of_forall (fun N => by positivity)
  · exact Eventually.of_forall (fun N => by
      dsimp [C]
      exact O.boundedLocalRoofDefect_density_le_scaledContributionCesaro start D N)

end OddOrbit
end Collatz3
