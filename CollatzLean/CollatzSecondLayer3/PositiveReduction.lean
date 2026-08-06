import CollatzLean.CollatzSecondLayer3.NormalizationObstruction

/-!
# 非有界odd-only軌道の無条件な正の三分岐

弱い第三対象であった「capture印付きfirst-crossing prefix」を廃止し、
persistent captureから実際に構成されたnormalization towerを第三対象とする。

主定理は解析原理・補集合・未証明principleを入力に取らない。
固定多項式の指数優越はLean内定理`polynomialBelowTwoPower`として使用する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

/-- persistent captureから第三の正対象を得る。 -/
theorem persistentCapture_to_normalizationObstruction
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPersistent : P.HasPersistentCapture) :
    Nonempty (NormalizationGeneratedObstructionTowerData O) :=
  ⟨P.toNormalizationGeneratedObstructionTower hPersistent⟩

/-- 標準prepared familyの無条件な正の二分岐。 -/
theorem preparedFullWindow_positive_dichotomy
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) :
    Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (NormalizationGeneratedObstructionTowerData O) := by
  rcases P.persistentCapture_or_polynomialSpecialC3 with
    hPersistent | hSpecial
  · exact Or.inr
      (persistentCapture_to_normalizationObstruction P hPersistent)
  · exact Or.inl hSpecial

/--
一つの非有界odd-only軌道を、三つの独立した正の数学対象へ還元する。
-/
theorem unboundedOrbit_positive_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (NormalizationGeneratedObstructionTowerData O) := by
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
    rcases preparedFullWindow_positive_dichotomy P with
      hSpecial | hNormalization
    · exact Or.inr (Or.inl hSpecial)
    · exact Or.inr (Or.inr hNormalization)

/--
非有界odd-only軌道の存在を、三つの正対象だけへ無条件に還元する。
-/
theorem unbounded_odd_orbit_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasNormalizationGeneratedObstructionTower := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hNormalization
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hNormalization⟩)

/-- 三つの正対象をすべて排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_positive_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasPolynomialSpecialC3Tower)
    (hNormalization : ¬ HasNormalizationGeneratedObstructionTower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_positive_trichotomy hGap hU with
    h | h | h
  · exact hMeander h
  · exact hSpecial h
  · exact hNormalization h

end CollatzSecondLayer3
