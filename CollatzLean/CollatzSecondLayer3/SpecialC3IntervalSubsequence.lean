import CollatzLean.CollatzSecondLayer3.SpecialC3AlignmentBasics
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# Special C3 terminal timeの無限部分列分類

自然数列は、ある値をcofinalに取るか、値が狭義増加する部分列を持つ。
これをsource-preserving Special C3 towerのterminal timeへ適用する。
増加枝では選択されたstartも狭義増加し、連続する二intervalは
`before`または真の`overlap`の二枝に縮む。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore

/-- 自然数列の定数cofinal部分列。 -/
structure ConstantNatSubsequenceData (a : ℕ → ℕ) where
  value : ℕ
  select : ℕ → ℕ
  select_strict : StrictMono select
  value_eq : ∀ n : ℕ, a (select n) = value

/-- 自然数列の値狭義増加部分列。 -/
structure IncreasingNatSubsequenceData (a : ℕ → ℕ) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  value_strict : StrictMono (fun n => a (select n))

/-- 最終的に`B`以下なら、有限値の一つがcofinalに現れる。 -/
private theorem cofinally_constant_of_eventually_le
    (a : ℕ → ℕ) :
    ∀ B : ℕ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n ≤ B) →
      ∃ v : ℕ, Cofinally (fun n => a n = v) := by
  intro B
  induction B with
  | zero =>
      rintro ⟨N, hN⟩
      refine ⟨0, ?_⟩
      intro M
      let n := max M N
      refine ⟨n, le_max_left M N, ?_⟩
      have hn := hN n (le_max_right M N)
      omega
  | succ B ih =>
      rintro ⟨N, hN⟩
      by_cases hTop : Cofinally (fun n => a n = B + 1)
      · exact ⟨B + 1, hTop⟩
      · obtain ⟨Ntop, hNtop⟩ :=
          Cofinally.eventually_not_of_not
            (fun n => a n = B + 1) hTop
        apply ih
        refine ⟨max N Ntop, ?_⟩
        intro n hn
        have hle := hN n (le_trans (le_max_left _ _) hn)
        have hne := hNtop n (le_trans (le_max_right _ _) hn)
        omega

/--
どの値もcofinalでなければ、列の値は任意の固定境界をcofinally越える。
-/
private theorem cofinally_gt_of_no_cofinal_constant
    (a : ℕ → ℕ)
    (hNo : ¬ ∃ v : ℕ, Cofinally (fun n => a n = v)) :
    ∀ B : ℕ, Cofinally (fun n => B < a n) := by
  intro B
  by_contra hNot
  obtain ⟨N, hN⟩ :=
    Cofinally.eventually_not_of_not
      (fun n => B < a n) hNot
  have hBound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n ≤ B := by
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    omega
  exact hNo (cofinally_constant_of_eventually_le a B hBound)

/-- 値を狭義増加させながら添字も狭義増加させる標準選択。 -/
private noncomputable def increasingValueSelect
    (a : ℕ → ℕ)
    (hLarge : ∀ B : ℕ, Cofinally (fun n => B < a n)) :
    ℕ → ℕ
  | 0 => Classical.choose ((hLarge 0) 0)
  | n + 1 =>
      Classical.choose
        ((hLarge (a (increasingValueSelect a hLarge n)))
          (increasingValueSelect a hLarge n + 1))

private theorem increasingValueSelect_index_strict
    (a : ℕ → ℕ)
    (hLarge : ∀ B : ℕ, Cofinally (fun n => B < a n)) :
    StrictMono (increasingValueSelect a hLarge) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs :=
    Classical.choose_spec
      ((hLarge (a (increasingValueSelect a hLarge n)))
        (increasingValueSelect a hLarge n + 1))
  simpa [increasingValueSelect] using hs.1

private theorem increasingValueSelect_value_strict
    (a : ℕ → ℕ)
    (hLarge : ∀ B : ℕ, Cofinally (fun n => B < a n)) :
    StrictMono (fun n => a (increasingValueSelect a hLarge n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs :=
    Classical.choose_spec
      ((hLarge (a (increasingValueSelect a hLarge n)))
        (increasingValueSelect a hLarge n + 1))
  simpa [increasingValueSelect] using hs.2

/-- 任意の自然数列は、cofinal定数部分列または値狭義増加部分列を持つ。 -/
theorem natSequence_constant_or_increasing_subsequence
    (a : ℕ → ℕ) :
    Nonempty (ConstantNatSubsequenceData a) ∨
      Nonempty (IncreasingNatSubsequenceData a) := by
  classical
  by_cases hConst : ∃ v : ℕ, Cofinally (fun n => a n = v)
  · obtain ⟨v, hv⟩ := hConst
    left
    exact ⟨{
      value := v
      select := Cofinally.select (fun n => a n = v) hv
      select_strict := Cofinally.select_strict (fun n => a n = v) hv
      value_eq := fun n => Cofinally.select_spec (fun n => a n = v) hv n
    }⟩
  · have hLarge := cofinally_gt_of_no_cofinal_constant a hConst
    right
    exact ⟨{
      select := increasingValueSelect a hLarge
      select_strict := increasingValueSelect_index_strict a hLarge
      value_strict := increasingValueSelect_value_strict a hLarge
    }⟩

namespace FutureMinimumSpecialC3TowerData

/-- terminal time列はcofinal定数または狭義増加部分列を持つ。 -/
theorem terminalTime_constant_or_increasing_subsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) :
    Nonempty (ConstantNatSubsequenceData R.terminalTime) ∨
      Nonempty (IncreasingNatSubsequenceData R.terminalTime) :=
  natSequence_constant_or_increasing_subsequence R.terminalTime

/-- 任意の狭義増加seed選択ではSpecial C3 lengthも狭義増加する。 -/
theorem length_strict_on_subsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {s : ℕ → ℕ}
    (hs : StrictMono s) :
    StrictMono (fun n => R.length (s n)) := by
  intro a b hab
  have hIndex : s a < s b := hs hab
  have hSelect : R.select (s a) < R.select (s b) :=
    R.select_strict hIndex
  simp only [length]
  omega

/-- cofinal定数terminal time部分列では全actual startが同じ。 -/
theorem start_eq_on_constantTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : ConstantNatSubsequenceData R.terminalTime)
    (n : ℕ) :
    R.start (S.select n) = R.anchor + S.value := by
  unfold start
  rw [S.value_eq n]

/-- cofinal定数terminal time部分列でもlengthは狭義増加する。 -/
theorem length_strict_on_constantTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : ConstantNatSubsequenceData R.terminalTime) :
    StrictMono (fun n => R.length (S.select n)) :=
  R.length_strict_on_subsequence S.select_strict

/-- terminal time増加部分列ではactual startも狭義増加する。 -/
theorem start_strict_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) :
    StrictMono (fun n => R.start (S.select n)) := by
  intro a b hab
  have ht :
      R.terminalTime (S.select a) <
        R.terminalTime (S.select b) :=
    S.value_strict hab
  change
    R.anchor + R.terminalTime (S.select a) <
      R.anchor + R.terminalTime (S.select b)
  exact Nat.add_lt_add_left ht R.anchor

/-- terminal time増加部分列でもlengthは狭義増加する。 -/
theorem length_strict_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) :
    StrictMono (fun n => R.length (S.select n)) :=
  R.length_strict_on_subsequence S.select_strict

/--
terminal time増加部分列の連続二項では、後のintervalが前へ戻る枝は消え、
前intervalが先に終わるか、二intervalが真にoverlapする。
-/
theorem before_or_overlap_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ) :
    R.SourceIntervalBefore (S.select n) (S.select (n + 1)) ∨
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1)) := by
  have hstart :
      R.start (S.select n) < R.start (S.select (n + 1)) :=
    R.start_strict_on_increasingTerminalSubsequence S (Nat.lt_succ_self n)
  by_cases hbefore :
      R.sourceIntervalEnd (S.select n) ≤
        R.sourceIntervalStart (S.select (n + 1))
  · exact Or.inl hbefore
  · right
    constructor
    · have hlenPos : 0 < R.length (S.select (n + 1)) := by
        simp [length]
      unfold sourceIntervalStart sourceIntervalEnd
      omega
    · unfold sourceIntervalStart sourceIntervalEnd at hbefore ⊢
      omega

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
