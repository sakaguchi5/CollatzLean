import CollatzLean.CollatzSecondLayer2.FirstDeferredRefinement
import CollatzLean.CollatzSecondLayer2.EventuallySynchronizedRefinement

/-!
# normalization obstructionの無条件refinement

標準normalization towerは既に無条件で

* first-deferred tower
* eventual-sync tower

へ分解される。

first-deferred側は`firstDeferredTower_refinement`で三対象へrefineされる。
eventual-sync側は周期指数tailを生むため、
`eventuallySynchronizedTower_impossible`によって直接排除される。

したがってstandard normalization towerからmeander枝は生成されず、
Polynomial Special C3または残余二構造だけが残る。
-/

namespace CollatzSecondLayer2

/--
標準normalization towerをPolynomial Special C3または残余二構造へ無条件に送る。
-/
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
    exact False.elim
      (eventuallySynchronizedTower_impossible E)

/-- Polynomial Special C3を除外した文脈では、standard towerは残余二構造へ入る。 -/
theorem standardNormalization_residual_of_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit}
    (hSpecial :
      ¬ Nonempty (PolynomialSpecialC3TowerData O))
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_refinement hGap D with
    hS | hR
  · exact False.elim (hSpecial hS)
  · exact hR

end CollatzSecondLayer2
