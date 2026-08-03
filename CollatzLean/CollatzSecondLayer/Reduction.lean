import CollatzLean.CollatzSecondLayer.SpecialC3
import CollatzLean.CollatzSecondLayer.CylinderUpgradeProof

/-!
# 非有界軌道の無限部分列型四分岐還元

有限terminal Listと有限SpecialC3存在を廃止し、

* one-sided meander
* 無限terminal抽出障害
* 閉じる出口の持続的無限部分列
* 深さ非有界な特殊C3部分列

の四分岐へ直接還元する。
-/

namespace CollatzSecondLayer

/-- 最終還元に必要な三つのbridge。 -/
structure ReductionBridge where
  movingCompactness : MovingCompactnessPrinciple
  cylinderUpgrade : CylinderUpgradePrinciple
  infiniteTerminalAnalysis : InfiniteTerminalAnalysisPrinciple

namespace ReductionBridge

/--
第一bridgeの証明と、Baker型算術入力から構成した第二bridgeを用いて、
最終的な第三bridgeだけを受け取るReductionBridgeを構成する。
-/
theorem ofArithmetic
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hInfinite : InfiniteTerminalAnalysisPrinciple) :
    ReductionBridge where
  movingCompactness := movingCompactnessPrinciple
  cylinderUpgrade := cylinderUpgradePrinciple_of_arithmetic hBaker hPow
  infiniteTerminalAnalysis := hInfinite

end ReductionBridge

/--
非有界odd-only軌道は、三つの例外または深さ非有界な特殊C3へ落ちる。
-/
theorem unbounded_orbit_reduction
    (B : ReductionBridge) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasInfiniteTerminalExtractionObstruction ∨
      HasPersistentAlternativeExit ∨
      HasArbitrarilyDeepSpecialC3 := by
  rintro ⟨O, hO⟩
  rcases B.movingCompactness O hO with ⟨D⟩
  rcases firstCrossingSequence_or_meander D with hMeander | hCrossing
  · exact Or.inl ⟨O, hO, hMeander⟩
  · rcases hCrossing with ⟨F⟩
    rcases B.cylinderUpgrade O F with ⟨S⟩
    rcases infiniteTerminalExtraction_split S with hObstruction | hExtraction
    · exact Or.inr (Or.inl hObstruction)
    · rcases hExtraction with ⟨E⟩
      rcases B.infiniteTerminalAnalysis O S E with ⟨A, hBranch⟩
      rcases hBranch with hAlternative | hSpecial
      · exact Or.inr (Or.inr (Or.inl ⟨O, S, E, A, hAlternative⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨O, S, E, A, hSpecial⟩))

/-- 三例外を排除すれば、非有界軌道は深さ非有界な特殊C3を導く。 -/
theorem arbitrarilyDeepSpecialC3_of_unbounded_of_no_exceptions
    (B : ReductionBridge)
    (hMeander : ¬ HasOneSidedMeander)
    (hExtraction : ¬ HasInfiniteTerminalExtractionObstruction)
    (hAlternative : ¬ HasPersistentAlternativeExit) :
    HasUnboundedOddOrbit → HasArbitrarilyDeepSpecialC3 := by
  intro hU
  rcases unbounded_orbit_reduction B hU with h | h | h | h
  · exact False.elim (hMeander h)
  · exact False.elim (hExtraction h)
  · exact False.elim (hAlternative h)
  · exact h

/--
三例外と深さ非有界な特殊C3を排除できれば、非有界odd-only軌道は存在しない。
-/
theorem no_unbounded_orbit
    (B : ReductionBridge)
    (hMeander : ¬ HasOneSidedMeander)
    (hExtraction : ¬ HasInfiniteTerminalExtractionObstruction)
    (hAlternative : ¬ HasPersistentAlternativeExit)
    (hSpecial : AsymptoticSpecialC3ExclusionPrinciple) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hSpecial
    (arbitrarilyDeepSpecialC3_of_unbounded_of_no_exceptions
      B hMeander hExtraction hAlternative hU)

end CollatzSecondLayer
