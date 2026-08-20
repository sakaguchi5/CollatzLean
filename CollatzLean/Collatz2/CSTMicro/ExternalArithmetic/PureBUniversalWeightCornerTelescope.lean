import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBAffineCornerTelescope
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.UniversalCutWeight

/-!
# Pure B: universal-weight corner telescope

`universalCutWeight` は primitive rank-unit を必要とせず

  3^m W_k = normalizedCutTerm(k) = 3 B_k   (mod G)

を満たす。

前段の affine telescope

  sum alpha_k B_k = A + G

を terminal-gap modulus に落とし、`3^m` を cancel すれば

  sum alpha_k W_k = sum W_k = 3q   (mod G)

を得る。

従って weighted-rank side も run gap `e_k=1` の cut を完全に消し、corners のみに
support を持つ。primitive 条件は不要。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

namespace MinimalActualABObstructionPacket

/-- actual first-failure exponent word を短く書く。 -/
private def cornerFailureWord
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : Collatz2.Word :=
  M.actual.firstFailureEdge.upperExponentWord

/-- first-failure upper word は actual minimal bad word の encoding。 -/
private theorem cornerFailureWord_eq_actualEncoding
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.cornerFailureWord = exponentWordOfParity M.word := by
  unfold cornerFailureWord
  unfold ActualABObstructionPacket.firstFailureEdge
  unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
  unfold FirstFailureProvenance.toFirstFailureEdge
  exact congrArg exponentWordOfParity M.failureStep_upperWord_eq_word

/-- pure odd depth と failure word oddSteps の一致。 -/
private theorem pureM_eq_cornerFailureOddSteps
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).m =
      Collatz2.Word.oddSteps M.cornerFailureWord := by
  let P := M.toPureBProfileObstruction hL
  have hM : P.m = oddCount M.word := by
    simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
  rw [M.cornerFailureWord_eq_actualEncoding]
  rw [oddSteps_exponentWordOfParity]
  exact hM

/-- pure terminal time と failure word twoSteps の一致。 -/
private theorem pureH_eq_cornerFailureTwoSteps
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).H =
      Collatz2.Word.twoSteps M.cornerFailureWord := by
  have hH := M.pureH_eq_actualWordLength hL
  have hFP := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  calc
    (M.toPureBProfileObstruction hL).H = M.word.length := hH
    _ = Collatz2.Word.twoSteps (exponentWordOfParity M.word) :=
      (hFP.twoSteps_exponentWordOfParity_eq_length hLen).symm
    _ = Collatz2.Word.twoSteps M.cornerFailureWord := by
      rw [M.cornerFailureWord_eq_actualEncoding]

/-- pure gap は failure word terminal gap。 -/
private theorem pureGap_eq_cornerFailureGap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).gap =
      Collatz2.Word.terminalGap M.cornerFailureWord := by
  let P := M.toPureBProfileObstruction hL
  have hH := M.pureH_eq_cornerFailureTwoSteps hL
  have hm := M.pureM_eq_cornerFailureOddSteps hL
  unfold PureBProfileObstruction.gap columnLayerGap Collatz2.Word.terminalGap
  rw [hH, hm]

/-- pure affine numerator は failure word affine constant。 -/
private theorem pureAffine_eq_cornerFailureAffine
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    profileAffineNumerator
        (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).h =
      Collatz2.Word.affineConst M.cornerFailureWord := by
  let P := M.toPureBProfileObstruction hL
  have hFP := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hRaw :=
    firstPassage_profileAffineNumerator_eq_wordAffineConst hFP hLen
  have hmWord :
      P.m = Collatz2.Word.oddSteps (exponentWordOfParity M.word) := by
    have hM : P.m = oddCount M.word := by
      simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
    rw [oddSteps_exponentWordOfParity]
    exact hM
  have hHfun : P.h = parityExtraDepth M.word := by
    funext k
    simp [P]
  rw [← hmWord, ← hHfun] at hRaw
  rw [M.cornerFailureWord_eq_actualEncoding]
  exact hRaw

/-- pure corner monomial は failure word affine prefix term。 -/
private theorem pureCornerMonomial_eq_failurePrefixTerm
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k < (M.toPureBProfileObstruction hL).m) :
    (M.toPureBProfileObstruction hL).profileCornerMonomial k =
      wordAffinePrefixTerm M.cornerFailureWord k := by
  let P := M.toPureBProfileObstruction hL
  have hEndpoint :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL (Nat.le_of_lt hk)
  have hWord := M.cornerFailureWord_eq_actualEncoding
  have hm := M.pureM_eq_cornerFailureOddSteps hL
  unfold PureBProfileObstruction.profileCornerMonomial wordAffinePrefixTerm
  rw [hEndpoint]
  rw [← hWord]
  rw [hm]

/--
weighted corner sum equals the ordinary universal cut-weight sum。
This is the primitive-free form of `(†)`。
-/
theorem universalWeight_corner_telescope
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    let F := M.actual.firstFailureEdge
    Finset.sum (Finset.range P.m)
      (fun k =>
        (P.profileCornerCoefficient k :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        Collatz2.Word.universalCutWeight
          F.upperExponentWord_firstCrossing k) =
      Collatz2.Word.universalCutWeightSum
        F.upperExponentWord_firstCrossing := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let hF : Collatz2.Word.FirstCrossing w :=
    F.upperExponentWord_firstCrossing
  let G := Collatz2.Word.terminalGap w
  have hw : w = M.cornerFailureWord := by rfl
  have hm : P.m = Collatz2.Word.oddSteps w := by
    simpa [P, w, hw] using M.pureM_eq_cornerFailureOddSteps hL
  have hGap : P.gap = G := by
    simpa [P, G, w, hw] using M.pureGap_eq_cornerFailureGap hL
  have hAffine :
      profileAffineNumerator P.m P.h = Collatz2.Word.affineConst w := by
    simpa [P, w, hw] using M.pureAffine_eq_cornerFailureAffine hL
  have hCornerNat := P.profileCornerMass_eq_affine_add_gap
  have hCornerMod :
      (P.profileCornerMass : ZMod G) =
        (Collatz2.Word.affineConst w : ZMod G) := by
    have hCast := congrArg (fun n : ℕ => (n : ZMod G)) hCornerNat
    push_cast at hCast
    rw [hAffine, hGap] at hCast
    have hGzero : ((G : ℕ) : ZMod G) = 0 := ZMod.natCast_self G
    rw [hGzero, add_zero] at hCast
    exact hCast
  apply hF.cancel_threePow
  have hLeftScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          Finset.sum (Finset.range P.m)
            (fun k =>
              (P.profileCornerCoefficient k : ZMod G) *
                Collatz2.Word.universalCutWeight hF k) =
        (3 : ZMod G) * (P.profileCornerMass : ZMod G) := by
    rw [Finset.mul_sum]
    calc
      Finset.sum (Finset.range P.m)
          (fun k =>
            (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
              ((P.profileCornerCoefficient k : ZMod G) *
                Collatz2.Word.universalCutWeight hF k))
          =
        Finset.sum (Finset.range P.m)
          (fun k =>
            (P.profileCornerCoefficient k : ZMod G) *
              ((Collatz2.Word.normalizedCutTerm w k : ℕ) : ZMod G)) := by
                apply Finset.sum_congr rfl
                intro k hkMem
                have hWeight := hF.threePow_mul_universalCutWeight k
                rw [← hWeight]
                ring
      _ =
        Finset.sum (Finset.range P.m)
          (fun k =>
            (P.profileCornerCoefficient k : ZMod G) *
              (3 * (P.profileCornerMonomial k : ZMod G))) := by
                apply Finset.sum_congr rfl
                intro k hkMem
                have hkP : k < P.m := Finset.mem_range.mp hkMem
                have hkW : k < Collatz2.Word.oddSteps w := by
                  rw [← hm]
                  exact hkP
                have hNorm :=
                  normalizedCutTerm_eq_three_mul_wordAffinePrefixTerm w hkW
                have hMono :
                    P.profileCornerMonomial k = wordAffinePrefixTerm w k := by
                  have h0 := M.pureCornerMonomial_eq_failurePrefixTerm hL hkP
                  simpa [w, hw] using h0
                rw [hNorm, ← hMono]
                push_cast
                rfl
      _ = (3 : ZMod G) * (P.profileCornerMass : ZMod G) := by
                unfold PureBProfileObstruction.profileCornerMass
                push_cast
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                ring
  have hRightScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          Collatz2.Word.universalCutWeightSum hF =
        (3 : ZMod G) *
          (Collatz2.Word.affineConst w : ZMod G) := by
    have h := hF.threePow_mul_universalCutWeightSum
    simpa [G, w] using h
  rw [hLeftScaled, hRightScaled, hCornerMod]

/--
actual first-failure specialization:
corner-supported universal weight sum is exactly `3q (mod G)`。
-/
theorem universalWeight_corner_telescope_eq_three_mul_q
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    let F := M.actual.firstFailureEdge
    Finset.sum (Finset.range P.m)
      (fun k =>
        (P.profileCornerCoefficient k :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        Collatz2.Word.universalCutWeight
          F.upperExponentWord_firstCrossing k) =
      (3 : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        (P.q : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  dsimp only
  rw [M.universalWeight_corner_telescope hL]
  have hSum := F.universalCutWeightSum_eq_three_mul_upperNormalizedDefectNat
  have hq : P.q = F.upperNormalizedDefectNat := by
    have hActual := M.toPureBProfileObstruction_q_eq hL
    have hCanonical := M.actual.q_eq_canonical
    dsimp [P, F]
    rw [hActual]
    exact hCanonical
  rw [hSum, hq]

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
