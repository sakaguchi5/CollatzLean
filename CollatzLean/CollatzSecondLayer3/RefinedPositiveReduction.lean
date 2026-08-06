import CollatzLean.CollatzSecondLayer3.NormalizationRefinement

/-!
# source-preserving normalization refinementを使う精密正還元
-/

namespace CollatzSecondLayer2

theorem unboundedOrbit_refined_positive_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases unboundedOrbit_standard_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hStandard
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hStandard with ⟨D⟩
    rcases standardNormalization_refinement hGap D with hSpecial' | hRefined
    · exact Or.inr (Or.inl hSpecial')
    · exact Or.inr (Or.inr hRefined)

theorem unboundedOrbit_refined_positive_quadrichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CriticalCaptureTowerData hGap O) ∨
      Nonempty (LongSynchronizedPlateauTowerData hGap O) := by
  rcases unboundedOrbit_refined_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hRefined
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hRefined with ⟨R⟩
    cases R with
    | criticalCapture C => exact Or.inr (Or.inr (Or.inl ⟨C⟩))
    | longSynchronizedPlateau P => exact Or.inr (Or.inr (Or.inr ⟨P⟩))

theorem unbounded_odd_orbit_refined_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasRefinedNormalizationObstructionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_refined_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hRefined
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hRefined⟩)

theorem no_unbounded_odd_orbit_of_refined_positive_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasPolynomialSpecialC3Tower)
    (hRefined : ¬ HasRefinedNormalizationObstructionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_refined_positive_trichotomy hGap hU with
    hM | hS | hR
  · exact hMeander hM
  · exact hSpecial hS
  · exact hRefined hR

end CollatzSecondLayer2
