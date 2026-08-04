import CollatzLean.CollatzSecondLayer2.AnalyticFourWay

/-!
# 解析的四分岐を経由する強い正の三分岐

既存の暫定還元とは異なり、persistent capture枝では
`CaptureNormalizationAnalyticFourWayPrinciple`を必ず経由する。
従って第三枝のcertificateはnormalization trajectoryに由来する。
-/

namespace CollatzSecondLayer2

/-- 標準prepared familyを解析的四分岐経由で最終三対象へ送る。 -/
theorem preparedFullWindow_strong_positive_reduction
    (hAnalytic : CaptureNormalizationAnalyticFourWayPrinciple)
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPow : PolynomialBelowTwoPower) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CaptureGeneratedCriticalExpansionTowerData O) := by
  classical
  by_cases hPersistent : P.HasPersistentCapture
  · exact persistentCapture_strong_positive_reduction
      hAnalytic P hPersistent
  · rcases P.persistentCapture_or_polynomialSpecialC3 hPow with
      hCapture | hSpecial
    · exact False.elim (hPersistent hCapture)
    · exact Or.inr (Or.inl hSpecial)

/--
一つの非有界odd-only軌道を、解析的四分岐を経由して三つの正対象へ還元する。
-/
theorem unboundedOrbit_strong_positive_trichotomy_on
    (hAnalytic : CaptureNormalizationAnalyticFourWayPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CaptureGeneratedCriticalExpansionTowerData O) := by
  classical
  let S : O.FutureMinimumSequence := O.futureMinimumSequence hU
  by_cases hM : ∃ j : ℕ, MeanderAt O (S.index j)
  · rcases hM with ⟨j, hj⟩
    exact Or.inl
      ⟨{
        unbounded := hU
        anchor := S.index j
        futureMinimum := S.futureMinimum j
        meander := hj
      }⟩
  · let F : MovingFirstCrossingData O :=
      movingFirstCrossingData_of_no_meander O hU S hM
    let P : PolynomialPreparedFullWindowFamily F :=
      polynomialPreparedFullWindowFamily hGap F
    exact preparedFullWindow_strong_positive_reduction
      hAnalytic P hPow

/--
非有界odd-only軌道の存在を、解析的四分岐を経由して三つの正対象だけへ還元する。
-/
theorem unbounded_odd_orbit_strong_positive_trichotomy
    (hAnalytic : CaptureNormalizationAnalyticFourWayPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasCaptureGeneratedCriticalExpansionTower := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_strong_positive_trichotomy_on
      hAnalytic hGap hPow O hU with
    hM | hSpecial | hCritical
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hCritical⟩)

/-- 強い三対象をすべて排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_strong_positive_exclusions
    (hAnalytic : CaptureNormalizationAnalyticFourWayPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasPolynomialSpecialC3Tower)
    (hCritical : ¬ HasCaptureGeneratedCriticalExpansionTower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_strong_positive_trichotomy
      hAnalytic hGap hPow hU with
    h | h | h
  · exact hMeander h
  · exact hSpecial h
  · exact hCritical h

end CollatzSecondLayer2
