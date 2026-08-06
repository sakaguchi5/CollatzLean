import CollatzLean.CollatzSecondLayer3.FirstCriticalTransition
import CollatzLean.CollatzSecondLayer3.EventuallySynchronizedRefinement

/-!
# 最終正還元：Special C3中央枝とfirst critical transition枝
-/

namespace CollatzSecondLayer2

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
      ⟨SpecialC3ObstructionTowerData.polynomial P.toPolynomialSpecialC3Tower⟩
  · by_cases hCritical : HasPersistentCriticalCapture T
    · exact Or.inr
        ⟨firstCriticalTransitionTowerOfPersistent T hPolynomial hCritical⟩
    · let R := superPolynomialNoCriticalOfExclusions T hPolynomial hCritical
      exact Or.inl
        ⟨SpecialC3ObstructionTowerData.discounted R.toDiscountedSpecialC3Tower⟩

theorem standardNormalization_final_refinement
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (FirstCriticalTransitionTowerData hGap O) := by
  rcases standardNormalization_outcomeTower_dichotomy D with hFirst | hEventually
  · rcases hFirst with ⟨T⟩
    exact firstDeferredTower_final_refinement hGap T
  · rcases hEventually with ⟨E⟩
    exact False.elim (eventuallySynchronizedTower_impossible E)

theorem unboundedOrbit_final_positive_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (FirstCriticalTransitionTowerData hGap O) := by
  rcases unboundedOrbit_standard_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hStandard
  · exact Or.inl hM
  · rcases hSpecial with ⟨S⟩
    exact Or.inr (Or.inl ⟨SpecialC3ObstructionTowerData.polynomial S⟩)
  · rcases hStandard with ⟨D⟩
    rcases standardNormalization_final_refinement hGap D with hSpecial' | hCritical
    · exact Or.inr (Or.inl hSpecial')
    · exact Or.inr (Or.inr hCritical)

theorem unboundedOrbit_final_positive_pentachotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (LargeExpandingDefectTransitionTowerData hGap O) ∨
      Nonempty (CaptureDenseTransitionTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases unboundedOrbit_final_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hCritical
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hCritical with ⟨R⟩
    rcases firstCriticalTransition_classification R with hLarge | hDense | hTerminal
    · exact Or.inr (Or.inr (Or.inl hLarge))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hDense)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTerminal)))

def HasFirstCriticalTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧
    Nonempty (FirstCriticalTransitionTowerData hGap O)

def HasLargeExpandingDefectTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧
    Nonempty (LargeExpandingDefectTransitionTowerData hGap O)

def HasCaptureDenseTransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧
    Nonempty (CaptureDenseTransitionTowerData hGap O)

def HasTerminalSpecialC3TransitionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧
    Nonempty (TerminalSpecialC3TransitionTowerData hGap O)

theorem unbounded_odd_orbit_final_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasFirstCriticalTransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hCritical
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hCritical⟩)

theorem unbounded_odd_orbit_final_positive_pentachotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasLargeExpandingDefectTransitionTower hGap ∨
      HasCaptureDenseTransitionTower hGap ∨
      HasTerminalSpecialC3TransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_positive_pentachotomy_on hGap O hU with
    hM | hSpecial | hLarge | hDense | hTerminal
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨O, hU, hLarge⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨O, hU, hDense⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨O, hU, hTerminal⟩)))

theorem no_unbounded_odd_orbit_of_final_positive_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasSpecialC3ObstructionTower)
    (hCritical : ¬ HasFirstCriticalTransitionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_final_positive_trichotomy hGap hU with hM | hS | hC
  · exact hMeander hM
  · exact hSpecial hS
  · exact hCritical hC

end CollatzSecondLayer2
