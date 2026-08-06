import CollatzLean.CollatzSecondLayer3.FirstDeferredRefinement
import CollatzLean.CollatzSecondLayer3.EventuallySynchronizedRefinement

/-!
# normalization obstructionの無条件refinement
-/

namespace CollatzSecondLayer2

theorem standardNormalization_refinement
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_outcomeTower_dichotomy D with
    hFirst | hEventually
  · rcases hFirst with ⟨F⟩
    rcases firstDeferredTower_refinement hGap O D F with
      hSpecial | hCritical | hPlateau
    · exact Or.inl hSpecial
    · exact Or.inr
        ⟨RefinedNormalizationObstructionTowerData.criticalCapture
          (Classical.choice hCritical)⟩
    · exact Or.inr
        ⟨RefinedNormalizationObstructionTowerData.longSynchronizedPlateau
          (Classical.choice hPlateau)⟩
  · rcases hEventually with ⟨E⟩
    exact False.elim (eventuallySynchronizedTower_impossible E)

theorem standardNormalization_residual_of_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    (hSpecial : ¬ Nonempty (PolynomialSpecialC3TowerData O))
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_refinement hGap D with hS | hR
  · exact False.elim (hSpecial hS)
  · exact hR

end CollatzSecondLayer2
