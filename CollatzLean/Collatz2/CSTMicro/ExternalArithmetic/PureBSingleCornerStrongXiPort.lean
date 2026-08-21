import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerSmallRootStage
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualXiFiniteCheck118

set_option linter.style.longLine false

/-!
# Pure B single-corner: strong Xi port, sharpened to precision 118

既存 strong window は `e >= 1538` を排除する。
`ActualXiFiniteCheck118` が有限範囲

  118 <= e < 1538

を exact native arithmetic で埋めるため、両者を合成して

  e >= 118
  x <= 16384 * (e+2)^15
  BoundaryXiCandidate e x
  --------------------------------
  False

を得る。

`117` では generic polynomial bound 以下の Xi candidate が実在するため、
この 118 は現在の generic residue bound に対する sharp finite threshold。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
既存 strong-window route: precision 1538 以上。
互換性のため theorem 名を保持する。
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

/--
finite exact scan による middle range `118 <= e < 1538` の排除。
-/
theorem no_actual_small_boundaryXiCandidate_between_118_1538
    {e x : ℕ}
    (h118 : 118 ≤ e)
    (h1538 : e < 1538)
    (hx :
      x ≤ boundaryFailureResidueBound rhinGapK rhinGapA e)
    (hCandidate : BoundaryXiCandidate e x) :
    False := by
  rcases hCandidate with ⟨m, hem, hResidue⟩
  have hXi :=
    criticalXiResidue_gt_boundaryFailureBound_of_118_le_lt_1538
      h118 h1538 hem
  have hModLe :
      x % (2 ^ e) ≤ x :=
    Nat.mod_le _ _
  have hBoundMod :
      x % (2 ^ e) ≤
        boundaryFailureResidueBound rhinGapK rhinGapA e :=
    le_trans hModLe hx
  rw [hResidue] at hBoundMod
  omega

/--
actual critical Xi に対する sharpened public exclusion。

118 以上は
* `118 <= e < 1538`: finite exact Xi scan
* `1538 <= e`: existing strong López--Stoll/Rhin route

で完全に覆う。
-/
theorem no_actual_small_boundaryXiCandidate_from_118
    (R : RhinLinearForm14)
    {e x : ℕ}
    (hLarge : 118 ≤ e)
    (hx :
      x ≤ boundaryFailureResidueBound rhinGapK rhinGapA e)
    (hCandidate : BoundaryXiCandidate e x) :
    False := by
  by_cases hSmall : e < 1538
  · exact
      no_actual_small_boundaryXiCandidate_between_118_1538
        hLarge hSmall hx hCandidate
  · have h1538 : 1538 ≤ e := by
      omega
    exact
      no_actual_small_boundaryXiCandidate_from_1538
        R h1538 hx hCandidate

namespace MinimalActualABObstructionPacket

/--
actual B representative の m-polynomial bound を precision e の
Stage-8 residue boundへ移す。

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
その rank が sharpened Xi range `e>=118` に入り、
さらに `m+1 <= e+2` なら contradiction。
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
    (hLarge : 118 ≤ beattyIndex (S.b - 1))
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
    no_actual_small_boundaryXiCandidate_from_118
      R hLarge hx hCandidate

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
