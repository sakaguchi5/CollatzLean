import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailLog196
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerStrongLeftReadyGeometry
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerActualLeftPrefix
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianOneShortSquareWindow196FromBHZ

set_option exponentiation.threshold 300

/-!
# Pure B single-corner: degree 196 localization -> Xi contradiction

one-short terminal localization と既存 criticalization-run bound

  criticalizationStart - b <= 18 + 15*ell

を足し合わせると

  m-b <= C196*(ell+1)^196 + 18 + 15*ell

を得る。

この width が `m/3` より小さければ既存 Beatty lower-slope argument により
StrongLeftReady が成立する。Xi port 自体は変更せず、precision threshold は
引き続き 118 のままである。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- degree 196 single-corner terminal width majorant。 -/
def singleCornerDyadicLog196Width
    (W : CriticalSturmianOneShortSquareWindow196)
    (ell : ℕ) : ℕ :=
  terminalOneShortSquareLog196Constant W * (ell + 1) ^ 196 +
    (18 + 15 * ell)

namespace MinimalActualABObstructionPacket

/-- single-corner left start `b` までの terminal distance の dyadic degree 196 bound。 -/
theorem singleCorner_m_sub_b_le_dyadicLog196
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    (M.toPureBProfileObstruction hL).m - S.b ≤
      singleCornerDyadicLog196Width W ell := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hStartPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  have hTail :=
    P.criticalizationTail_le_dyadicOneShortSquareLog196
      W R hy hStartPos
      (by simpa [P] using hmSize)
  have hLeft :=
    M.singleCorner_criticalizationStart_sub_b_le_dyadic15
      R hL S hmSize
  have hStartLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  dsimp [P, singleCornerDyadicLog196Width] at hTail hLeft hStartLe ⊢
  omega

/--
explicit threshold を満たす single-corner actual bad packet は存在しない。
Xi numeric large condition は従来どおり `119<=m`。
-/
theorem singleCorner_impossible_of_dyadicLog196_strongThreshold
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hmLarge : 119 ≤ (M.toPureBProfileObstruction hL).m)
    (hThreshold :
      3 * singleCornerDyadicLog196Width W ell + 1 ≤
        (M.toPureBProfileObstruction hL).m) :
    False := by
  let P := M.toPureBProfileObstruction hL
  have hWidth :=
    M.singleCorner_m_sub_b_le_dyadicLog196 W R hL S hmSize
  have hWidth' :
      P.m - S.b ≤ singleCornerDyadicLog196Width W ell := by
    simpa [P] using hWidth
  have hThird : 3 * (P.m - S.b) + 1 ≤ P.m := by
    have hMul :
        3 * (P.m - S.b) ≤
          3 * singleCornerDyadicLog196Width W ell :=
      Nat.mul_le_mul_left 3 hWidth'
    have hThreshold' :
        3 * singleCornerDyadicLog196Width W ell + 1 ≤ P.m := by
      simpa [P] using hThreshold
    omega
  have hReady : S.StrongLeftReady :=
    S.strongLeftReady_of_large_and_three_tail
      (by simpa [P] using hmLarge)
      hThird
  have hDivRaw := M.singleCorner_leftPrefixDivisibility hL S
  have hDiv : M.SingleCornerLeftPrefixDivisibility hL S := by
    simpa [MinimalActualABObstructionPacket.SingleCornerLeftPrefixDivisibility]
      using hDivRaw
  exact M.singleCorner_impossible_of_strongLeftReady R hL S hDiv hReady

/-- card-one actual branch 用 wrapper。 -/
theorem singleCorner_card_one_impossible_of_dyadicLog196_strongThreshold
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hmLarge : 119 ≤ (M.toPureBProfileObstruction hL).m)
    (hThreshold :
      3 * singleCornerDyadicLog196Width W ell + 1 ≤
        (M.toPureBProfileObstruction hL).m) :
    False := by
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  exact
    M.singleCorner_impossible_of_dyadicLog196_strongThreshold
      W R hL S hmSize hmLarge hThreshold

/--
exact BHZ + Rhin から構成した actual degree 196 window を直接差し込む wrapper。
-/
theorem singleCorner_card_one_impossible_of_actualBHZ196_strongThreshold
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hmLarge : 119 ≤ (M.toPureBProfileObstruction hL).m)
    (hThreshold :
      3 * singleCornerDyadicLog196Width
            (actualCriticalSturmianOneShortSquareWindow196 R) ell + 1 ≤
        (M.toPureBProfileObstruction hL).m) :
    False := by
  exact
    M.singleCorner_card_one_impossible_of_dyadicLog196_strongThreshold
      (actualCriticalSturmianOneShortSquareWindow196 R)
      R hL hCard hmSize hmLarge hThreshold

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
