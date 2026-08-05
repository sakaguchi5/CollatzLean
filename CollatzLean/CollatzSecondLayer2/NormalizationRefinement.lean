import CollatzLean.CollatzSecondLayer2.FirstDeferredRefinement

/-!
# normalization obstructionのrefinement

標準normalization towerは既に無条件で

* first-deferred tower
* eventual-sync tower

へ分解される。first-deferred側は`firstDeferredTower_refinement`で実際に証明済みであり、
外部の局所証明義務を入力に取らない。残る入力は、eventual-sync towerをactualな
anchored meanderへ送る`EventuallySynchronizedTowerToMeanderPrinciple`だけである。
-/

namespace CollatzSecondLayer2

/--
標準normalization towerを既存二枝と残余二構造へ送る。
first-deferred側は実定理、eventual-sync側だけを局所原理として受け取る。
-/
theorem standardNormalization_refinement
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_outcomeTower_dichotomy D with
    hFirst | hEventually
  · rcases hFirst with ⟨F⟩
    rcases firstDeferredTower_refinement hGap hPow O D F with
      hSpecial | hCritical | hPlateau
    · exact Or.inr (Or.inl hSpecial)
    · exact Or.inr (Or.inr
        ⟨RefinedNormalizationObstructionTowerData.criticalCapture
          (Classical.choice hCritical)⟩)
    · exact Or.inr (Or.inr
        ⟨RefinedNormalizationObstructionTowerData.longSynchronizedPlateau
          (Classical.choice hPlateau)⟩)
  · rcases hEventually with ⟨E⟩
    exact Or.inl (hSync hGap O D E)

/-- 既存二対象を除外した文脈では、standard towerは残余二構造へ入る。 -/
theorem standardNormalization_residual_of_exclusions
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    {O : OddOrbit}
    (hMeander : ¬ Nonempty (AnchoredOneSidedMeanderData O))
    (hSpecial : ¬ Nonempty (PolynomialSpecialC3TowerData O))
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_refinement
      hSync hGap hPow D with hM | hS | hR
  · exact False.elim (hMeander hM)
  · exact False.elim (hSpecial hS)
  · exact hR

end CollatzSecondLayer2
