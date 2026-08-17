import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelHeightFour
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinTwoThreeGap14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongTwoLogDyadicSlack

/-!
# Step 8: explicit strong-window slack with start = 9

Step 7 の polynomial bound は

  B(e) = 16384 * (e+2)^15

を与える。
strong window では必要な最終 inequality は

  4 q_j (B(q_j+q_{j+1}-1)+1)
    < 2^(q_{j-1}-1).

このファイルでは、Rhin + continued-fraction denominator growth + finite checks
から最終的に得るべきこの pure-integer domination を明示 certificate として切り出し、
既存 `StrongTwoLogDyadicSlack` を完全に構成する。

また `start=9`, `q_8=485`, `q_9=1054` から
strong first precision が exact に `1538` であることも導く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Rhin/continued-fraction 側の Step 8 最終 integer certificate。
`dominates` は transcendence theorem ではなく、その theorem と denominator-growth
計算を済ませた後に Lean へ渡す最終算術形。
-/
structure RhinStrongSlackStartNineCertificate
    (D : OrientedCriticalContinuedFractionData) where
  start_eq_nine : D.base.start = 9
  q_eight : D.base.q 8 = 485
  q_nine : D.base.q 9 = 1054

  dominates :
    ∀ j : ℕ,
      9 ≤ j →
      4 * D.base.q j *
          (boundaryFailureResidueBound
              rhinGapK rhinGapA
              (strongDenominatorWindowUpper D.base.q j) + 1)
        < 2 ^ (D.base.q (j - 1) - 1)

namespace RhinStrongSlackStartNineCertificate

/--
Step 6 の一様 height bound `H = 4` と
Step 8 の start-nine certificate から、
strong dyadic slack を構成する。
-/
theorem toStrongTwoLogDyadicSlack
    {D : OrientedCriticalContinuedFractionData}
    (G : CriticalChristoffelHeightGeometry D)
    (R : RhinStrongSlackStartNineCertificate D) :
    StrongTwoLogDyadicSlack
      G.toChristoffelHeightInstantiation
      (boundaryFailureResidueBound rhinGapK rhinGapA) := by
  refine {
    bound_mono :=
      boundaryFailureResidueBound_mono rhinGapK rhinGapA
    previous_denominator_pos := ?_
    dominates := ?_
  }
  · intro j _hjStart
    exact D.q_pos_all (j - 1)
  · intro j hjStart
    have hjStartBase :
        D.base.start ≤ j := by
      change D.base.start ≤ j at hjStart
      exact hjStart
    have hjNine :
        9 ≤ j := by
      rw [R.start_eq_nine] at hjStartBase
      exact hjStartBase
    change
      4 * D.base.q j *
          (boundaryFailureResidueBound
              rhinGapK rhinGapA
              (strongDenominatorWindowUpper D.base.q j) + 1)
        <
      2 ^ (D.base.q (j - 1) - 1)
    exact R.dominates j hjNine

/-- Step 8 certificate は actual family の start を exact に 9 と固定する。 -/
theorem lopezStoll_start_eq_nine
    {D : OrientedCriticalContinuedFractionData}
    (R : RhinStrongSlackStartNineCertificate D) :
    D.toCriticalChristoffelPacket.toLopezStollInstantiation.start = 9 := by
  exact R.start_eq_nine

/-- strong window の最初の covered precision は exact に 1538。 -/
theorem strongFirstPrecision_eq_1538
    {D : OrientedCriticalContinuedFractionData}
    (R : RhinStrongSlackStartNineCertificate D) :
    strongFirstPrecision
      D.toCriticalChristoffelPacket.toLopezStollInstantiation = 1538 := by
  change
    D.base.q (D.base.start - 1) + D.base.q D.base.start - 1 = 1538
  rw [R.start_eq_nine]
  norm_num
  rw [R.q_eight, R.q_nine]

end RhinStrongSlackStartNineCertificate

end ExternalArithmetic
end CSTMicro
end Collatz2
