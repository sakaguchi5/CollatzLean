import CollatzLean.Collatz3.Core.BoundaryForm
import CollatzLean.Collatz3.Geometry.IntegerFerrersDeficit
import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn

/-!
# Collatz3: current A integer budget bridge

`CanonicalEndpointFloorContractingReturn` の actual affine translation `B` を
二方向から評価する。

word / critical-profile 側:

  Bcrit = IntegerFerrersDeficit + B

actual boundary 側:

  B = contractionCompensation + positiveReturnCost

これらを接続して、Collatz3 最初の exact integer budget

  Bcrit
    = IntegerFerrersDeficit
      + contractionCompensation
      + positiveReturnCost

を得る。

この段階では `ZMod` を使わず、全項を自然数の正方向に保持する。
-/

namespace Collatz3

open Collatz2

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A の actual start value。 -/
def startValue
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  O.value D.startIndex

/-- current A の actual terminal value。 -/
def endValue
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  O.value D.endIndex

/-- current A の actual positive return gap。 -/
def returnGap
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  endValue D - startValue D

/-- current A の coefficient gap `2^H-3^p`。 -/
def coefficientGap
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  2 ^ Collatz2.Word.twoSteps D.word -
    3 ^ Collatz2.Word.oddSteps D.word

/-- contracting なのに source heightを維持するための cost。 -/
def contractionCompensation
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  coefficientGap D * startValue D

/-- actual frame を `start -> end` へ右移動するための cost。 -/
def positiveReturnCost
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  2 ^ Collatz2.Word.twoSteps D.word * returnGap D

/-- current A の critical-roof affine budget。 -/
def criticalBudget
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  Collatz3.Word.criticalAffineConst
    (Collatz2.Word.oddSteps D.word)

/-- current A の integer Ferrers deficit。 -/
def integerFerrersDeficit
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) : ℕ :=
  Collatz3.Word.integerFerrersDeficit D.word

/-- current A の word-side FirstCrossing。 -/
theorem wordFirstCrossing
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    Collatz2.Word.FirstCrossing D.word := by
  simpa [Collatz2.OddOrbit.CanonicalEndpointFloorContractingReturn.word] using
    D.firstCrossing

/-- current A の actual run は affine realization を与える。 -/
theorem wordRealizes
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    Collatz2.Word.Realizes D.word (startValue D) (endValue D) := by
  simpa [
    startValue,
    endValue,
    Collatz2.OddOrbit.CanonicalEndpointFloorContractingReturn.word
  ] using D.runs.realizes

/-- current A の coefficient は contracting。 -/
theorem oddCoeff_le_twoCoeff
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    (Collatz2.AffineTransfer.ofWord D.word).oddCoeff ≤
      (Collatz2.AffineTransfer.ofWord D.word).twoCoeff := by
  change
    3 ^ Collatz2.Word.oddSteps D.word ≤
      2 ^ Collatz2.Word.twoSteps D.word
  exact Nat.le_of_lt
    ((Collatz2.Word.contracting_iff_threePow_lt_twoPow).1 D.contracting)

/-- current A は strict positive return。 -/
theorem startValue_lt_endValue
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    startValue D < endValue D := by
  simpa [startValue, endValue,
    Collatz2.OddOrbit.CanonicalEndpointFloorContractingReturn.endIndex] using
    D.positive

/--
BoundaryForm 側の exact decomposition:

  B = G*x + 2^H*(y-x).
-/
theorem affineConst_eq_contractionCompensation_add_positiveReturnCost
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    Collatz2.Word.affineConst D.word =
      contractionCompensation D + positiveReturnCost D := by
  have hR :
      (Collatz2.AffineTransfer.ofWord D.word).Realizes
        (startValue D) (endValue D) := by
    simpa [Collatz2.Word.Realizes] using wordRealizes D
  have hEq :=
    Collatz3.AffineTransfer.translate_eq_contractionCompensation_add_positiveReturnCost
      hR
      (oddCoeff_le_twoCoeff D)
      (Nat.le_of_lt (startValue_lt_endValue D))
  simpa [
    Collatz2.AffineTransfer.ofWord,
    Collatz2.AffineTransfer.contractionCompensation,
    Collatz2.AffineTransfer.positiveReturnCost,
    Collatz2.AffineTransfer.contractionGap,
    contractionCompensation,
    positiveReturnCost,
    coefficientGap,
    returnGap,
    startValue,
    endValue
  ] using hEq
/--
Collatz3 最初の exact integer budget theorem。

  Bcrit
    = IntegerFerrersDeficit
      + contractionCompensation
      + positiveReturnCost.

全項は `ℕ` 上にあり、modular cancellation をまだ導入していない。
-/
theorem criticalBudget_eq_integerFerrersDeficit_add_contractionCompensation_add_positiveReturnCost
    {O : Collatz2.OddOrbit}
    (D : O.CanonicalEndpointFloorContractingReturn) :
    criticalBudget D =
      integerFerrersDeficit D +
        contractionCompensation D +
        positiveReturnCost D := by
  have hCritical :=
    Collatz3.Word.criticalAffineConst_eq_integerFerrersDeficit_add_affineConst
      (wordFirstCrossing D)
  have hBoundary :=
    affineConst_eq_contractionCompensation_add_positiveReturnCost D
  calc
    criticalBudget D
        = integerFerrersDeficit D + Collatz2.Word.affineConst D.word := by
            simpa [criticalBudget, integerFerrersDeficit] using hCritical
    _ = integerFerrersDeficit D +
          (contractionCompensation D + positiveReturnCost D) := by
            rw [hBoundary]
    _ = integerFerrersDeficit D +
          contractionCompensation D + positiveReturnCost D := by
            ring

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz3
