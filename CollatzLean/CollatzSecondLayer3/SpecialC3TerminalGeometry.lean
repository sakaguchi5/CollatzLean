import CollatzLean.CollatzSecondLayer3.SpecialC3CriticalOverlapAlignment

/-!
# Special C3 terminal geometryの三分岐

terminal time列を、既存の

* cofinal定数部分列
* terminal time狭義増加部分列

へ分ける。増加部分列では各連続pairが`before ∨ overlap`であるため、
overlapがcofinalに現れるか、ある時点以降すべてbeforeになるかへさらに分ける。

これによりsource-preserving Special C3 towerの幾何学的残余枝を

* Constant terminal
* Increasing disjoint tail
* Increasing cofinal overlap

の三枝として明示する。cofinal overlap枝の各選択pairには
`CriticalOverlapAlignmentData`を自動付加できる。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- terminal time増加部分列で、ある時点以降すべての連続intervalがbeforeになる枝。 -/
structure IncreasingBeforeTailData
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) where
  cutoff : ℕ
  before : ∀ n : ℕ, cutoff ≤ n →
    R.SourceIntervalBefore (S.select n) (S.select (n + 1))

/-- terminal time増加部分列で、overlap pairがcofinalに現れる枝。 -/
structure IncreasingOverlapCofinalData
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  overlap : ∀ n : ℕ,
    R.SourceIntervalsOverlap
      (S.select (select n))
      (S.select (select n + 1))

/--
増加terminal部分列では、eventual-beforeまたはcofinal-overlapのどちらかになる。
-/
theorem increasing_beforeTail_or_overlapCofinal
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) :
    Nonempty (IncreasingBeforeTailData R S) ∨
      Nonempty (IncreasingOverlapCofinalData R S) := by
  classical
  let P : ℕ → Prop := fun n =>
    R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))
  by_cases hOverlap : Cofinally P
  · right
    exact ⟨{
      select := Cofinally.select P hOverlap
      select_strict := Cofinally.select_strict P hOverlap
      overlap := fun n => Cofinally.select_spec P hOverlap n
    }⟩
  · left
    obtain ⟨N, hN⟩ :=
      Cofinally.eventually_not_of_not P hOverlap
    exact ⟨{
      cutoff := N
      before := by
        intro n hn
        rcases R.before_or_overlap_on_increasingTerminalSubsequence S n with
          hBefore | hOv
        · exact hBefore
        · exact False.elim ((hN n hn) hOv)
    }⟩

/--
source-preserving Special C3 towerのterminal geometry三分岐。
-/
inductive TerminalGeometryAlternative
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) : Type where
  | constant
      (S : ConstantNatSubsequenceData R.terminalTime)
  | increasingBefore
      (S : IncreasingNatSubsequenceData R.terminalTime)
      (B : IncreasingBeforeTailData R S)
  | increasingOverlap
      (S : IncreasingNatSubsequenceData R.terminalTime)
      (C : IncreasingOverlapCofinalData R S)

/-- 任意のsource-preserving Special C3 towerは上の三枝のどれかへ入る。 -/
theorem terminalGeometry_trichotomy
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) :
    Nonempty (TerminalGeometryAlternative R) := by
  classical
  rcases R.terminalTime_constant_or_increasing_subsequence with
    hConstant | hIncreasing
  · rcases hConstant with ⟨S⟩
    exact ⟨TerminalGeometryAlternative.constant S⟩
  · rcases hIncreasing with ⟨S⟩
    rcases R.increasing_beforeTail_or_overlapCofinal S with
      hBefore | hOverlap
    · rcases hBefore with ⟨B⟩
      exact ⟨TerminalGeometryAlternative.increasingBefore S B⟩
    · rcases hOverlap with ⟨C⟩
      exact ⟨TerminalGeometryAlternative.increasingOverlap S C⟩

namespace IncreasingOverlapCofinalData

/--
cofinal-overlap枝の各選択pairへcritical one-bit alignment dataを付加する。
-/
noncomputable def criticalAlignment
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {S : IncreasingNatSubsequenceData R.terminalTime}
    (C : IncreasingOverlapCofinalData R S)
    (n : ℕ) :
    CriticalOverlapAlignmentData R S (C.select n) :=
  R.criticalOverlapAlignmentData S (C.select n) (C.overlap n)

/-- cofinal-overlap枝では選択された全pairで開始kernelが奇数。 -/
theorem criticalStartKernel_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {S : IncreasingNatSubsequenceData R.terminalTime}
    (C : IncreasingOverlapCofinalData R S)
    (n : ℕ) :
    Odd (C.criticalAlignment n).startKernel :=
  (C.criticalAlignment n).startKernel_odd

/-- cofinal-overlap枝では選択された全pairで開始差が`2^(H+1) * odd`にexact分解される。 -/
theorem start_exact_alignment
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {S : IncreasingNatSubsequenceData R.terminalTime}
    (C : IncreasingOverlapCofinalData R S)
    (n : ℕ) :
    R.center (S.select (C.select n + 1)) -
          R.transportedCenterFromLeft
            (S.select (C.select n))
            (S.select (C.select n + 1)) =
        (2 : ℤ) ^
            (twoSteps
                (R.overlapWord
                  (S.select (C.select n))
                  (S.select (C.select n + 1))) + 1) *
          (C.criticalAlignment n).startKernel ∧
      Odd (C.criticalAlignment n).startKernel := by
  constructor
  · exact (C.criticalAlignment n).startDifference
  · exact (C.criticalAlignment n).startKernel_odd

/-- cofinal-overlap枝では選択された全pairで共通word輸送後の差がexactに`2 * odd`。 -/
theorem finish_exact_one_bit
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {S : IncreasingNatSubsequenceData R.terminalTime}
    (C : IncreasingOverlapCofinalData R S)
    (n : ℕ) :
    R.rightOverlapTransportFinish
          (S.select (C.select n))
          (S.select (C.select n + 1)) -
        R.leftOverlapTransportFinish
          (S.select (C.select n))
          (S.select (C.select n + 1)) =
        2 * (C.criticalAlignment n).finishKernel ∧
      Odd (C.criticalAlignment n).finishKernel := by
  constructor
  · exact (C.criticalAlignment n).finishDifference
  · exact (C.criticalAlignment n).finishKernel_odd

end IncreasingOverlapCofinalData

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
