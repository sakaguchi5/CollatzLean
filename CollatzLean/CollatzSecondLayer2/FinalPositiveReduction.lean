import CollatzLean.CollatzSecondLayer2.FirstCriticalTransition
import CollatzLean.CollatzSecondLayer2.EventuallySynchronizedRefinement

/-!
# 最終正還元：Special C3中央枝とfirst critical transition枝

long synchronized plateauは最終対象から除き、その生成元である
super-polynomial no-critical towerをdiscounted Special C3へ直接送る。

persistent critical枝は最初のcritical時刻を保存した
`FirstCriticalTransitionTowerData`へ強化する。

最終三分岐は

* anchored one-sided meander
* Special C3 obstruction
  * Polynomial Special C3
  * Discounted Special C3
* first critical transition tower

である。third branchはさらに

* large expanding defect
* capture-dense transition
* terminal Special C3

へ分かれる。terminal Special C3は中央枝へ吸収しない。
-/

namespace CollatzSecondLayer2

/-- first-deferred towerをSpecial C3中央枝またはfirst-critical枝へ送る。 -/
theorem firstDeferredTower_final_refinement
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) :
    Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (FirstCriticalTransitionTowerData hGap O) := by
  classical
  by_cases hPolynomial : HasPersistentPolynomialTerminalBound T
  · let P := polynomialTerminalTowerOfPersistent T hPolynomial
    exact Or.inl
      ⟨SpecialC3ObstructionTowerData.polynomial
        P.toPolynomialSpecialC3Tower⟩
  · by_cases hCritical : HasPersistentCriticalCapture T
    · exact Or.inr
        ⟨firstCriticalTransitionTowerOfPersistent
          T hPolynomial hCritical⟩
    · let R :=
        superPolynomialNoCriticalOfExclusions
          T hPolynomial hCritical
      exact Or.inl
        ⟨SpecialC3ObstructionTowerData.discounted
          R.toDiscountedSpecialC3Tower⟩

/--
standard normalization towerをSpecial C3中央枝またはfirst-critical枝へ送る。
eventual synchronizationは直接矛盾する。
-/
theorem standardNormalization_final_refinement
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (FirstCriticalTransitionTowerData hGap O) := by
  rcases standardNormalization_outcomeTower_dichotomy D with
    hFirst | hEventually
  · rcases hFirst with ⟨T⟩
    exact firstDeferredTower_final_refinement hGap T
  · rcases hEventually with ⟨E⟩
    exact False.elim (eventuallySynchronizedTower_impossible E)

/-- 一つの非有界軌道に対する最終無条件三分岐。 -/
theorem unboundedOrbit_final_positive_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (FirstCriticalTransitionTowerData hGap O) := by
  rcases unboundedOrbit_standard_positive_trichotomy_on
      hGap O hU with hM | hSpecial | hStandard
  · exact Or.inl hM
  · rcases hSpecial with ⟨S⟩
    exact Or.inr (Or.inl
      ⟨SpecialC3ObstructionTowerData.polynomial S⟩)
  · rcases hStandard with ⟨D⟩
    rcases standardNormalization_final_refinement hGap D with
      hSpecial' | hCritical
    · exact Or.inr (Or.inl hSpecial')
    · exact Or.inr (Or.inr hCritical)

/-- first-critical内部三枝まで展開した最終五分岐。 -/
theorem unboundedOrbit_final_positive_pentachotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (LargeExpandingDefectTransitionTowerData hGap O) ∨
      Nonempty (CaptureDenseTransitionTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases unboundedOrbit_final_positive_trichotomy_on
      hGap O hU with hM | hSpecial | hCritical
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hCritical with ⟨R⟩
    rcases firstCriticalTransition_classification R with
      hLarge | hDense | hTerminal
    · exact Or.inr (Or.inr (Or.inl hLarge))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hDense)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTerminal)))

/-- 非有界軌道上のfirst critical transition tower。 -/
def HasFirstCriticalTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (FirstCriticalTransitionTowerData hGap O)

/-- 非有界軌道上のlarge expanding defect transition tower。 -/
def HasLargeExpandingDefectTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (LargeExpandingDefectTransitionTowerData hGap O)

/-- 非有界軌道上のcapture-dense transition tower。 -/
def HasCaptureDenseTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (CaptureDenseTransitionTowerData hGap O)

/-- 非有界軌道上のterminal Special C3 transition tower。 -/
def HasTerminalSpecialC3TransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O)

/-- 非有界odd-only軌道に対する最終三分岐。 -/
theorem unbounded_odd_orbit_final_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasFirstCriticalTransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_positive_trichotomy_on
      hGap O hU with hM | hSpecial | hCritical
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hCritical⟩)

/-- first-critical内部三枝まで展開した非有界軌道の最終五分岐。 -/
theorem unbounded_odd_orbit_final_positive_pentachotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasLargeExpandingDefectTransitionTower hGap ∨
      HasCaptureDenseTransitionTower hGap ∨
      HasTerminalSpecialC3TransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_positive_pentachotomy_on
      hGap O hU with hM | hSpecial | hLarge | hDense | hTerminal
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨O, hU, hLarge⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨O, hU, hDense⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨O, hU, hTerminal⟩)))

/-- 最終三対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_final_positive_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasSpecialC3ObstructionTower)
    (hCritical : ¬ HasFirstCriticalTransitionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_final_positive_trichotomy
      hGap hU with hM | hS | hC
  · exact hMeander hM
  · exact hSpecial hS
  · exact hCritical hC

end CollatzSecondLayer2
