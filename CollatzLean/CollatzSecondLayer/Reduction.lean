import CollatzLean.CollatzSecondLayer.SpecialC3

/-!
# 非有界軌道の四分岐還元

三種類の非接続枝を例外として明示し、それ以外を特殊C3へ送る。
未解決の数学的橋は `ReductionBridge` の三フィールドとして公開する。
-/

namespace CollatzSecondLayer

/--
最終還元に必要な三つの上流bridge。

1. 非有界軌道からmoving-limitデータを抽出する。
2. 長大first-crossing列をpolynomial-small canonical C3列へ昇格する。
3. 抽出済みterminal chainへ有限解析packetを供給する。

これらを `axiom` とせず、最終定理の明示的引数にしている。
-/
structure ReductionBridge where
  movingCompactness : MovingCompactnessPrinciple
  cylinderUpgrade : CylinderUpgradePrinciple
  terminalAnalysis : TerminalAnalysisPrinciple

/--
非有界odd-only軌道は、次の四つのいずれかへ落ちる。

* one-sided meander
* terminal chain抽出障害
* 特殊C3になる前の別出口
* 特殊C3有限障害
-/
theorem unbounded_orbit_reduction
    (B : ReductionBridge) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasTerminalExtractionObstruction ∨
      HasAlternativeExit ∨
      HasSpecialC3 := by
  rintro ⟨O, hO⟩
  rcases B.movingCompactness O hO with ⟨D⟩
  rcases firstCrossingSequence_or_meander D with hMeander | hCrossing
  · exact Or.inl ⟨O, hO, hMeander⟩
  · rcases hCrossing with ⟨F⟩
    rcases B.cylinderUpgrade O F with ⟨S⟩
    rcases terminalExtraction_split S with hObstruction | hTerminal
    · exact Or.inr (Or.inl hObstruction)
    · rcases hTerminal with ⟨T⟩
      rcases B.terminalAnalysis O S T with ⟨P⟩
      rcases alternativeExit_or_specialC3 P with hExit | hSpecial
      · exact Or.inr (Or.inr (Or.inl hExit))
      · exact Or.inr (Or.inr (Or.inr hSpecial))

/--
三例外を別途排除できれば、非有界軌道は特殊C3の存在を導く。
-/
theorem specialC3_of_unbounded_of_no_exceptions
    (B : ReductionBridge)
    (hMeander : ¬ HasOneSidedMeander)
    (hExtraction : ¬ HasTerminalExtractionObstruction)
    (hExit : ¬ HasAlternativeExit) :
    HasUnboundedOddOrbit → HasSpecialC3 := by
  intro hU
  rcases unbounded_orbit_reduction B hU with h | h | h | h
  · exact False.elim (hMeander h)
  · exact False.elim (hExtraction h)
  · exact False.elim (hExit h)
  · exact h

/--
さらに特殊C3も排除できれば、非有界odd-only軌道は存在しない。
-/
theorem no_unbounded_orbit
    (B : ReductionBridge)
    (hMeander : ¬ HasOneSidedMeander)
    (hExtraction : ¬ HasTerminalExtractionObstruction)
    (hExit : ¬ HasAlternativeExit)
    (hSpecial : ¬ HasSpecialC3) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hSpecial
    (specialC3_of_unbounded_of_no_exceptions
      B hMeander hExtraction hExit hU)

end CollatzSecondLayer
