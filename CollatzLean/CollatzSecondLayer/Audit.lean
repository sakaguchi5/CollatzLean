import CollatzLean.CollatzSecondLayer.Reduction

/-!
# 第二層の監査

このファイルは公開する最終型を固定する。
`axiom`、`sorry`、`admit`は使用しない。
-/

namespace CollatzSecondLayer

#check OddOrbit
#check MovingLimitData
#check FirstCrossingSequenceData
#check C3CylinderSequence
#check TerminalPairData
#check SpecialC3Data
#check unbounded_orbit_reduction
#check specialC3_of_unbounded_of_no_exceptions
#check no_unbounded_orbit

example (B : ReductionBridge) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasTerminalExtractionObstruction ∨
      HasAlternativeExit ∨
      HasSpecialC3 :=
  unbounded_orbit_reduction B

end CollatzSecondLayer
