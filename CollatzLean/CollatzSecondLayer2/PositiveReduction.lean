import CollatzLean.CollatzSecondLayer2.PositiveObjects


/-!
# persistent captureから正の三対象への中央還元

標準prepared full-window familyを構成し、十分後の各項を
captureまたはpolynomial Special C3へ送る。
persistent captureなら、同じmoving first-crossing項の長いproper-prefix膨張を
capture witnessと束ね、capture-generated critical expansion towerを得る。
-/

namespace CollatzSecondLayer2

/-- persistent captureから第三の正対象を得る。 -/
theorem persistentCapture_to_criticalExpansionTower
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPersistent : P.HasPersistentCapture) :
    Nonempty (CaptureGeneratedCriticalExpansionTowerData O) :=
  ⟨P.toCriticalExpansionTower hPersistent⟩

/-- 標準prepared familyの正の二分岐。 -/
theorem preparedFullWindow_positive_dichotomy
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPow : PolynomialBelowTwoPower) :
    Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CaptureGeneratedCriticalExpansionTowerData O) := by
  rcases P.persistentCapture_or_polynomialSpecialC3 hPow with
    hPersistent | hSpecial
  · exact Or.inr (persistentCapture_to_criticalExpansionTower P hPersistent)
  · exact Or.inl hSpecial

/--
一つの非有界odd-only軌道を、三つの正の数学対象へ還元する。
-/
theorem unboundedOrbit_positive_trichotomy_on
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
    rcases preparedFullWindow_positive_dichotomy P hPow with
      hSpecial | hCritical
    · exact Or.inr (Or.inl hSpecial)
    · exact Or.inr (Or.inr hCritical)

/--
非有界odd-only軌道の存在を、三つの正の数学対象だけへ還元する。
-/
theorem unbounded_odd_orbit_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasCaptureGeneratedCriticalExpansionTower := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_positive_trichotomy_on hGap hPow O hU with
    hM | hSpecial | hCritical
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hCritical⟩)

/-- 三つの正対象をすべて排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_positive_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasPolynomialSpecialC3Tower)
    (hCritical : ¬ HasCaptureGeneratedCriticalExpansionTower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_positive_trichotomy hGap hPow hU with
    h | h | h
  · exact hMeander h
  · exact hSpecial h
  · exact hCritical h

end CollatzSecondLayer2
