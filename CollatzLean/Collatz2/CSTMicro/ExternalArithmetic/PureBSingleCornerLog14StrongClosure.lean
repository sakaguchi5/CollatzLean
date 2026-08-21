import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerStrongLeftReadyGeometry
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerActualLeftPrefix

/-!
# Pure B single-corner: log14 localization -> Strong Xi contradiction

前段を最終的に接続する。

  T(ell) = terminalSquareLog14Constant W * (ell+1)^14 + 18 + 15*ell

と置く。single-corner localization は `m-b<=T(ell)`。
従って

  3*T(ell)+1 <= m

なら `3*(m-b)+1<=m`、さらに `m>=1539` なら StrongLeftReady。
left prefix divisibility は actual theorem から自動供給されるので、既存 Strong Xi port により
single-corner bad packet は contradiction になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Stage 4/5 closure 用の explicit dyadic terminal width majorant。 -/
def singleCornerDyadicLog14Width
    (W : CriticalSturmianSquareWindow14)
    (ell : ℕ) : ℕ :=
  terminalSquareLog14Constant W * (ell + 1) ^ 14 +
    (18 + 15 * ell)

namespace MinimalActualABObstructionPacket

/--
explicit threshold を満たす single-corner actual bad packet は存在しない。
-/
theorem singleCorner_impossible_of_dyadicLog14_strongThreshold
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hmLarge :
      1539 ≤ (M.toPureBProfileObstruction hL).m)
    (hThreshold :
      3 * singleCornerDyadicLog14Width W ell + 1 ≤
        (M.toPureBProfileObstruction hL).m) :
    False := by
  let P := M.toPureBProfileObstruction hL
  have hWidth :=
    M.singleCorner_m_sub_b_le_dyadicLog14 W R hL S hmSize
  have hWidth' :
      P.m - S.b ≤ singleCornerDyadicLog14Width W ell := by
    simpa [P, singleCornerDyadicLog14Width] using hWidth
  have hThird :
      3 * (P.m - S.b) + 1 ≤ P.m := by
    have hMul :
        3 * (P.m - S.b) ≤
          3 * singleCornerDyadicLog14Width W ell :=
      Nat.mul_le_mul_left 3 hWidth'
    have hThreshold' :
        3 * singleCornerDyadicLog14Width W ell + 1 ≤ P.m := by
      simpa [P] using hThreshold
    omega
  have hReady : S.StrongLeftReady :=
    S.strongLeftReady_of_large_and_three_tail
      (by simpa [P] using hmLarge)
      hThird
  have hDivRaw := M.singleCorner_leftPrefixDivisibility hL S
  have hDiv : M.SingleCornerLeftPrefixDivisibility hL S := by
    simpa [MinimalActualABObstructionPacket.SingleCornerLeftPrefixDivisibility] using hDivRaw
  exact M.singleCorner_impossible_of_strongLeftReady R hL S hDiv hReady

/-- card-one actual branch 用 wrapper。 -/
theorem singleCorner_card_one_impossible_of_dyadicLog14_strongThreshold
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hmLarge :
      1539 ≤ (M.toPureBProfileObstruction hL).m)
    (hThreshold :
      3 * singleCornerDyadicLog14Width W ell + 1 ≤
        (M.toPureBProfileObstruction hL).m) :
    False := by
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  exact
    M.singleCorner_impossible_of_dyadicLog14_strongThreshold
      W R hL S hmSize hmLarge hThreshold

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
