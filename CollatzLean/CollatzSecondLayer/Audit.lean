import CollatzLean.CollatzSecondLayer.Reduction

/-!
# 第二層・無限部分列型還元の監査

有限terminal Listは公開型から除去されている。
最終障害は有限SpecialC3一個ではなく、深さ非有界な特殊C3部分列である。
`axiom`、`sorry`、`admit`は使用しない。
-/

namespace CollatzSecondLayer

#check OddOrbit
#check MovingLimitData
#check FirstCrossingSequenceData
#check C3CylinderSequence
#check TerminalPairData
#check InfiniteTerminalExtraction
#check InfiniteTerminalAnalysis
#check PersistentAlternativeExitData
#check ArbitrarilyDeepSpecialC3Data
#check HasInfiniteTerminalExtractionObstruction
#check HasPersistentAlternativeExit
#check HasArbitrarilyDeepSpecialC3
#check InfiniteTerminalAnalysisPrinciple
#check AsymptoticSpecialC3ExclusionPrinciple
#check unbounded_orbit_reduction
#check arbitrarilyDeepSpecialC3_of_unbounded_of_no_exceptions
#check no_unbounded_orbit

example (B : ReductionBridge) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasInfiniteTerminalExtractionObstruction ∨
      HasPersistentAlternativeExit ∨
      HasArbitrarilyDeepSpecialC3 :=
  unbounded_orbit_reduction B

end CollatzSecondLayer
