import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualCriticalFiniteScan
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualRhinStrongSlack
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryFiniteCheck1538
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalASteps6to8

set_option linter.style.longLine false

/-!
# Actual Boundary A closure from the single external Rhin interface

このファイルが strong A route の最終 assembler。
外から受け取るのは `RhinLinearForm14` だけであり、

* critical convergent/Farey data,
* parity orientation,
* Beatty corridor,
* finite Xi matching,
* Christoffel H=4,
* denominator growth and start-nine slack,
* finite range e<1538,

はすべて Lean 内で構成する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Steps 6--8 actual packet constructed from the one Rhin theorem. -/
theorem actualCriticalASteps6to8
    (R : RhinLinearForm14) :
    CriticalASteps6to8 actualOrientedCriticalContinuedFractionData := {
  heightGeometry := actualCriticalChristoffelHeightGeometry
  rhinGap := R.toRhinTwoThreePowerGap14
  strongSlack := R.toActualStrongSlackStartNine
}

/--
Final Boundary A elimination.
No mathematical hypothesis remains except the reviewed `RhinLinearForm14` interface.
-/
theorem boundaryA_eliminated_from_RhinLinearForm14
    (R : RhinLinearForm14) :
    ∀ v : ParityWord,
      IsFerrersBoundary v →
      2 < v.length →
      WordPureSeparation v := by
  let X68 := actualCriticalASteps6to8 R
  let L :=
    actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket.toLopezStollInstantiation
  have hMatch : StrongBoundaryLopezStollMatch L := by
    have hI :=
      actualCriticalSturmianFiniteScanIdentity.toCriticalFiniteXiIdentity
    exact
      hI.toStrongBoundaryLopezStollMatch
        actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket
  have hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          rhinGapK * (p + 1) ^ rhinGapA *
            (2 ^ H - 3 ^ p) :=
    X68.boundaryGap
  have hFirst : strongFirstPrecision L = 1538 := by
    change strongFirstPrecision
      actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket.toLopezStollInstantiation = 1538
    exact X68.firstPrecision_eq_1538
  have hFinite := actualBoundaryFiniteCheck1538 (L := L) hFirst
  exact
    boundaryA_eliminated_from_strong_actual_family
      X68.heightFour hMatch hGap X68.strongDyadicSlack hFinite

end ExternalArithmetic
end CSTMicro
end Collatz2
