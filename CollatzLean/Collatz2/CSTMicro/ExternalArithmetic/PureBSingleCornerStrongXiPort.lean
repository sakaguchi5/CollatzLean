import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerSmallRootStage
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin

set_option linter.style.longLine false

/-!
# Pure B single-corner: strong Xi port

Stage 4 の large-side 排除で使う strong arithmetic port。

既存 `smallXiCandidate_precision_le` は record packing 用の粗い degree-14 bound を返す。
large-m 排除ではそれを反転するより、Stage 8 で既に構成済みの strong window を直接使う方が強い。

actual critical family では

  strongFirstPrecision = 1538

であり、`RhinLinearForm14` から

  * corrected López--Stoll strong matching,
  * Christoffel height H=4,
  * strong dyadic slack

がすべて構成済みである。従って precision `e >= 1538` で

  x <= 16384 * (e+2)^15

を満たす `BoundaryXiCandidate e x` は存在しない。

このファイルは、その既存 Stage 8 closure を single-corner 左側から直接呼べる
public wrapper にする。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
actual corrected family に対する strong small-Xi exclusion。

Boundary A 専用の statement ではなく、同じ finite Xi target を持つ任意の
`BoundaryXiCandidate` にそのまま適用できる。
-/
theorem no_actual_small_boundaryXiCandidate_from_1538
    (R : RhinLinearForm14)
    {e x : ℕ}
    (hLarge : 1538 ≤ e)
    (hx :
      x ≤ boundaryFailureResidueBound rhinGapK rhinGapA e)
    (hCandidate : BoundaryXiCandidate e x) :
    False := by
  let X68 := actualCriticalASteps6to8 R
  let L :=
    actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket.toLopezStollInstantiation
  have hMatch : StrongBoundaryLopezStollMatch L := by
    have hI :=
      actualCriticalSturmianFiniteScanIdentity.toCriticalFiniteXiIdentity
    exact
      hI.toStrongBoundaryLopezStollMatch
        actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket
  have hFirst : strongFirstPrecision L = 1538 := by
    change strongFirstPrecision
      actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket.toLopezStollInstantiation = 1538
    exact X68.firstPrecision_eq_1538
  have hLarge' : strongFirstPrecision L ≤ e := by
    rw [hFirst]
    exact hLarge
  exact
    no_small_boundaryXiCandidate_eventually_strong
      X68.heightFour
      hMatch
      X68.strongDyadicSlack.toStrongWindowHeightSqueeze
      hLarge'
      hx
      hCandidate

namespace MinimalActualABObstructionPacket

/--
actual B representative の m-polynomial bound を、precision e の Stage-8 residue boundへ移す。

必要なのは `m+1 <= e+2` だけ。
-/
theorem actualRepresentative_le_strongXiBound_of_m_le_precision
    (R : RhinLinearForm14)
    {L e : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hm :
      (M.toPureBProfileObstruction hL).m + 1 ≤ e + 2) :
    M.actual.firstFailureEdge.step.edge.upperR ≤
      boundaryFailureResidueBound rhinGapK rhinGapA e := by
  have hR := M.actualRepresentative_le_rhinPolynomial R hL
  have hPow :
      ((M.toPureBProfileObstruction hL).m + 1) ^ 15 ≤
        (e + 2) ^ 15 :=
    Nat.pow_le_pow_left hm 15
  unfold boundaryFailureResidueBound rhinGapA
  exact le_trans hR (Nat.mul_le_mul_left rhinGapK hPow)

/--
left critical-prefix divisibility が actual trace から供給され、
その rank が strong range に入り、さらに `m+1 <= e+2` なら contradiction。

ここで

  e = beta(b-1).

したがって Stage 4 の large-left branch は、残りを purely geometric な
`b` の大きさ評価へ還元できる。
-/
theorem singleCorner_left_impossible_of_strongRange
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hDiv :
      (2 : ℤ) ^ beattyIndex (S.b - 1) ∣
        (3 : ℤ) ^ (S.b - 1) *
            (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          criticalPrefixPhiZ (S.b - 1))
    (hLarge : 1538 ≤ beattyIndex (S.b - 1))
    (hm :
      (M.toPureBProfileObstruction hL).m + 1 ≤
        beattyIndex (S.b - 1) + 2) :
    False := by
  have hCandidate :
      BoundaryXiCandidate
        (beattyIndex (S.b - 1))
        M.actual.firstFailureEdge.step.edge.upperR :=
    boundaryXiCandidate_of_threePow_add_criticalPrefix_dvd hDiv
  have hx :
      M.actual.firstFailureEdge.step.edge.upperR ≤
        boundaryFailureResidueBound
          rhinGapK rhinGapA (beattyIndex (S.b - 1)) :=
    M.actualRepresentative_le_strongXiBound_of_m_le_precision
      R hL hm
  exact
    no_actual_small_boundaryXiCandidate_from_1538
      R hLarge hx hCandidate

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
