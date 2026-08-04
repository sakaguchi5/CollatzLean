import CollatzLean.CollatzSecondLayer2.NormalizationRefinement

/-!
# source-preserving normalization refinementを使う精密正還元

既存の無条件raw三分岐はそのまま残す。このファイルは、標準構成由来を保持した
強化版第三枝と二つの局所refinement原理から、最終的な精密三分岐・四分岐を導く。
-/

namespace CollatzSecondLayer2

/-- 一つの非有界軌道に対する精密三分岐。 -/
theorem unboundedOrbit_refined_positive_trichotomy_on
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases unboundedOrbit_standard_positive_trichotomy_on
      hGap hPow O hU with hM | hSpecial | hStandard
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hStandard with ⟨D⟩
    exact standardNormalization_refinement
      hSync hDeferred hGap hPow D

/-- 精密第三枝をcritical capture / long plateauへ展開した四分岐。 -/
theorem unboundedOrbit_refined_positive_quadrichotomy_on
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CriticalCaptureTowerData hGap O) ∨
      Nonempty (LongSynchronizedPlateauTowerData hGap O) := by
  rcases unboundedOrbit_refined_positive_trichotomy_on
      hSync hDeferred hGap hPow O hU with
    hM | hSpecial | hRefined
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hRefined with ⟨R⟩
    cases R with
    | criticalCapture C =>
        exact Or.inr (Or.inr (Or.inl ⟨C⟩))
    | longSynchronizedPlateau P =>
        exact Or.inr (Or.inr (Or.inr ⟨P⟩))

/-- 非有界odd-only軌道に対する精密三分岐。 -/
theorem unbounded_odd_orbit_refined_positive_trichotomy
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasRefinedNormalizationObstructionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_refined_positive_trichotomy_on
      hSync hDeferred hGap hPow O hU with
    hM | hSpecial | hRefined
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hRefined⟩)

/-- refined三対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_refined_positive_exclusions
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasPolynomialSpecialC3Tower)
    (hRefined : ¬ HasRefinedNormalizationObstructionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_refined_positive_trichotomy
      hSync hDeferred hGap hPow hU with hM | hS | hR
  · exact hMeander hM
  · exact hSpecial hS
  · exact hRefined hR

end CollatzSecondLayer2
