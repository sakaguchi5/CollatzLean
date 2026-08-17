import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalStrongMatchProof
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinStrongSlackStartNine

/-!
# Boundary A Steps 6--8 packet

Step 6:
  explicit Christoffel finite balance -> `H = 4`

Step 7:
  Rhin-type integer corollary -> `K = 16384`, `A = 14`

Step 8:
  start-nine denominator/slack certificate -> `StrongTwoLogDyadicSlack`
  and `strongFirstPrecision = 1538`

Steps 1--5 の strong matching packet と独立に構成できる。
最終 A closure では両者を同じ actual family 上で合流させる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalASteps6to8
    (D : OrientedCriticalContinuedFractionData) where
  heightGeometry : CriticalChristoffelHeightGeometry D
  rhinGap : RhinTwoThreePowerGap14
  strongSlack : RhinStrongSlackStartNineCertificate D

namespace CriticalASteps6to8

/-- Step 6 output。 -/
def heightFour
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalASteps6to8 D) :
    ChristoffelHeightInstantiation
      D.toCriticalChristoffelPacket.toLopezStollInstantiation :=
  X.heightGeometry.toChristoffelHeightInstantiation

@[simp] theorem heightFour_H
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalASteps6to8 D) :
    X.heightFour.H = 4 := rfl

/-- Step 7 output。 -/
theorem boundaryGap
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalASteps6to8 D) :
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤
        rhinGapK * (p + 1) ^ rhinGapA *
          (2 ^ H - 3 ^ p) :=
  X.rhinGap.boundary_gap

/-- Step 8 output。 -/
theorem strongDyadicSlack
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalASteps6to8 D) :
    StrongTwoLogDyadicSlack
      X.heightFour
      (boundaryFailureResidueBound rhinGapK rhinGapA) :=
  X.strongSlack.toStrongTwoLogDyadicSlack X.heightGeometry

/-- Step 8 numeric cutoff。 -/
theorem firstPrecision_eq_1538
    {D : OrientedCriticalContinuedFractionData}
    (X : CriticalASteps6to8 D) :
    strongFirstPrecision
      D.toCriticalChristoffelPacket.toLopezStollInstantiation = 1538 :=
  X.strongSlack.strongFirstPrecision_eq_1538

end CriticalASteps6to8

end ExternalArithmetic
end CSTMicro
end Collatz2
