import CollatzLean.CollatzExternal.LopezStoll
import CollatzLean.CollatzSecondLayer3.GenericObstructions
import CollatzLean.CollatzSecondLayer3.FutureMinimumGenericReduction
import CollatzLean.CollatzSecondLayer3.FinalTerminalReduction

/-!
# 臨界meanderの最終吸収

future-minimumからのordered normalizationを直接用いることで、
López–Stoll密度を使わずにone-sided meanderをgeneric最終対象へ吸収する。
従来の密度入力付きAPIとgeneric二分岐APIは互換用として残す。

現行のdirect還元ではdeep lower-replay source towerが排除済みなので、
非有界軌道はsource-preserving Special C3 tower、従ってgeneric Special C3 towerを生成する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

/--
López–Stoll臨界密度からone-sided meanderをgeneric最終二対象へ吸収する
bridge statement。実際にはfuture-minimum構造だけで証明できる。
-/
def CriticalMeanderAbsorptionPrinciple : Prop :=
  ∀ O : OddOrbit,
    ∀ M : AnchoredOneSidedMeanderData O,
      CriticalExponentDensityAt O M.anchor →
        Nonempty (GenericSpecialC3TowerData O) ∨
        Nonempty (GenericDeepLowerReplayTowerData O)

/-- Critical meander absorption principleは密度入力を使わずに成立する。 -/
theorem criticalMeanderAbsorptionPrinciple :
    CriticalMeanderAbsorptionPrinciple := by
  intro O M _hDensity
  exact
    futureMinimum_generic_obstruction_dichotomy
      O M.unbounded M.anchor M.futureMinimum

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

/-- 密度bridgeによりmeanderを吸収した従来互換の最終二分岐。 -/
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

/--
外部gap・密度・meander bridgeを使わないgeneric単一対象排除形。
generic Special C3 towerを排除すれば非有界odd-only軌道は存在しない。
-/
theorem no_unbounded_odd_orbit_of_genericSpecialC3_exclusion_direct
    (hSpecial : ¬ HasGenericSpecialC3Tower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hSpecial
    (unboundedOrbit_genericSpecialC3Tower_direct hU)

/--
従来互換のdirect二対象排除形。
deep lower-replay排除仮定は不要になったが、既存利用箇所のため引数を残す。
-/
theorem no_unbounded_odd_orbit_of_generic_exclusions_direct
    (hSpecial : ¬ HasGenericSpecialC3Tower)
    (_hDeep : ¬ HasGenericDeepLowerReplayTower) :
    ¬ HasUnboundedOddOrbit :=
  no_unbounded_odd_orbit_of_genericSpecialC3_exclusion_direct hSpecial

end CollatzSecondLayer3
