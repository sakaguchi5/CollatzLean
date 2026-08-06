import CollatzLean.CollatzExternal.LopezStoll
import CollatzLean.CollatzSecondLayer3.GenericObstructions
import CollatzLean.CollatzSecondLayer3.FinalTerminalReduction

/-!
# 臨界meanderの最終吸収

López–Stoll密度入力と、densityからprepared normalizationへ接続する
project-specific bridgeを明示的に分離する。最終還元は生成履歴を持たない
Special C3 / deep lower-replayの二対象だけを返す。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

/--
López–Stoll臨界密度からone-sided meanderをgeneric最終二対象へ吸収する
正確なbridge statement。外部密度のodd-only翻訳とは別に監査できる。
-/
def CriticalMeanderAbsorptionPrinciple : Prop :=
  ∀ O : OddOrbit,
    ∀ M : AnchoredOneSidedMeanderData O,
      CriticalExponentDensityAt O M.anchor →
        Nonempty (GenericSpecialC3TowerData O) ∨
        Nonempty (GenericDeepLowerReplayTowerData O)

/-- 現行三分岐をsource-independent三分岐へ忘却する。 -/
theorem unboundedOrbit_generic_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  rcases unboundedOrbit_final_terminal_trichotomy_on hGap O hU with
    hM | hS | hD
  · exact Or.inl hM
  · rcases hS with ⟨S⟩
    exact Or.inr (Or.inl ⟨S.toGeneric⟩)
  · rcases hD with ⟨D⟩
    exact Or.inr (Or.inr ⟨D.toGeneric⟩)

/-- 密度bridgeによりmeanderを吸収した最終二分岐。 -/
theorem unboundedOrbit_generic_dichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (hDensity : LopezStollCriticalDensityPrinciple)
    (hAbsorb : CriticalMeanderAbsorptionPrinciple)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  rcases unboundedOrbit_generic_trichotomy_on hGap O hU with hM | hS | hD
  · rcases hM with ⟨M⟩
    exact hAbsorb O M (hDensity O hU M.anchor)
  · exact Or.inl hS
  · exact Or.inr hD

/-- generic最終二対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_generic_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hDensity : LopezStollCriticalDensityPrinciple)
    (hAbsorb : CriticalMeanderAbsorptionPrinciple)
    (hSpecial : ¬ HasGenericSpecialC3Tower)
    (hDeep : ¬ HasGenericDeepLowerReplayTower) :
    ¬ HasUnboundedOddOrbit := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_generic_dichotomy_on
      hGap hDensity hAbsorb O hU with hS | hD
  · exact hSpecial ⟨O, hU, hS⟩
  · exact hDeep ⟨O, hU, hD⟩

end CollatzSecondLayer3
