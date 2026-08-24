import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalPredFusion
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellMinimalityPacket

/-!
# Attached terminal fused RHS と terminal-top Farey packet の exact comparison

`AttachedTerminalPredFusion` の右辺

  2^e * Z_c + 2

を、actual minimal B の terminal top predecessor が持つ

  residue D,
  representative increment deltaR

と exact に比較する。

中心点は三つある。

1. pure witness は actual minimal word では `y = R + q` なので、
   terminal critical state を prefix side へ戻すと `q` が exact に消える。
2. `deltaR = 2^position * fareyLocalInverse` と inverse equation により、
   `3^c * deltaR` は `2^position + 2^length * localQuotient` に exact 化する。
3. residue を同じ local quotient で展開すると、最終的に
   `G-D` と `deltaR-R` の二つの strict clearance を持つ balance が得られる。

このファイル自体では、その balance の右辺に残る
`profileAffineLocalPrefixZ c` をさらに消去することはしない。
そこが次の exact gluing target である。
-/

namespace Collatz2
namespace CSTMicro

namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
terminal critical start `c` の integral state を prefix side へ戻した exact identity。

  2^beta(c) Z_c
    = localPrefix(c) + 3^c (y-q).

`c` は genuine terminal critical suffix の start なので、full affine numerator を
prefix と critical suffix に exact 分割できる。
-/
theorem terminalCritical_integralState_scaled_eq_localPrefix_add_y_sub_q
    (P : PureBProfileObstruction) :
    let c := P.terminalCriticalStart
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I c
        P.criticalizationStart_le_terminalCriticalStart
        P.terminalCriticalStart_spec.1
    (2 : ℤ) ^ beattyIndex c * Z =
      P.profileAffineLocalPrefixZ c +
        (3 : ℤ) ^ c * (P.y - (P.q : ℤ)) := by
  dsimp
  let c := P.terminalCriticalStart
  let I := P.criticalizationStart_spec
  let Z :=
    P.integralCriticalTailStateInt
      I c
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  have hCLe : c ≤ P.m := by
    dsimp [c]
    exact P.terminalCriticalStart_spec.1
  have hState :=
    P.integralCriticalTailStateInt_spec
      I
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  have hAffine :=
    P.profileAffineNumerator_cast_eq_prefix_add_criticalInterval
      P.terminalCriticalStart_spec
  have hPrefix :=
    P.profileAffinePrefixZ_factor hCLe
  have hDeep := P.profileAffine_sub_gap_mul_y_eq_deep
  have hGap := P.gap_cast_eq_twoPow_terminal_sub_threePow
  have hBetaLe : beattyIndex c ≤ beattyIndex P.m := by
    by_cases hcm : c = P.m
    · rw [hcm]
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m =
        beattyIndex c + (beattyIndex P.m - beattyIndex c) := by
    omega
  have hThreeSplit :
      (3 : ℤ) ^ P.m =
        (3 : ℤ) ^ (P.m - c) * (3 : ℤ) ^ c := by
    have hm : P.m = (P.m - c) + c := by omega
    rw [hm, pow_add]
    simp
  have hRawScaled :
      (3 : ℤ) ^ (P.m - c) *
          ((2 : ℤ) ^ beattyIndex c * Z) =
        (2 : ℤ) ^ (beattyIndex P.m + 1) * P.y -
          (2 : ℤ) ^ beattyIndex c *
            criticalIntervalPhiZ c P.m := by
    calc
      (3 : ℤ) ^ (P.m - c) *
          ((2 : ℤ) ^ beattyIndex c * Z)
          =
        (2 : ℤ) ^ beattyIndex c *
          ((3 : ℤ) ^ (P.m - c) * Z) := by ring
      _ =
        (2 : ℤ) ^ beattyIndex c * P.terminalRawTail c := by
          dsimp [c, I, Z] at hState ⊢
          rw [hState]
      _ =
        (2 : ℤ) ^ (beattyIndex P.m + 1) * P.y -
          (2 : ℤ) ^ beattyIndex c *
            criticalIntervalPhiZ c P.m := by
          unfold terminalRawTail
          rw [hBetaSplit, pow_add, pow_succ]
          ring_nf
          simp
  have hDeepScaled :
      (2 : ℤ) ^ (beattyIndex P.m + 1) * P.y -
          (2 : ℤ) ^ beattyIndex c *
            criticalIntervalPhiZ c P.m =
        (3 : ℤ) ^ (P.m - c) *
          (P.profileAffineLocalPrefixZ c +
            (3 : ℤ) ^ c * (P.y - (P.q : ℤ))) := by
    dsimp [c] at hAffine hPrefix
    rw [hAffine, hPrefix, hGap] at hDeep
    rw [hThreeSplit] at hDeep
    ring_nf at hDeep ⊢
    linarith
  have hCancel :
      (3 : ℤ) ^ (P.m - c) *
          ((2 : ℤ) ^ beattyIndex c * Z) =
        (3 : ℤ) ^ (P.m - c) *
          (P.profileAffineLocalPrefixZ c +
            (3 : ℤ) ^ c * (P.y - (P.q : ℤ))) := by
    exact hRawScaled.trans hDeepScaled
  have hPowNe : (3 : ℤ) ^ (P.m - c) ≠ 0 := by
    positivity
  have hFinal := mul_left_cancel₀ hPowNe hCancel
  dsimp [c, I, Z] at hFinal ⊢
  exact hFinal

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/--
minimal actual B から作った pure packet では

  y - q = leastRepresentative(B)

が exact に成り立つ。
-/
theorem toPureBProfileObstruction_y_sub_q_eq_leastRepresentative
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).y -
        ((M.toPureBProfileObstruction hL).q : ℤ) =
      (leastRepresentative M.word : ℤ) := by
  have hUpper :
      M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
    unfold ActualABObstructionPacket.firstFailureEdge
    unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
    unfold FirstFailureProvenance.toFirstFailureEdge
    dsimp
    exact M.failureStep_upperWord_eq_word
  rw [M.toPureBProfileObstruction_y_eq_upperR_add_q hL]
  rw [M.toPureBProfileObstruction_q_eq hL]
  unfold AdjacentFerrersSwap.upperR
  rw [hUpper]
  ring

end MinimalActualABObstructionPacket

end ExternalArithmetic

/-! ## Farey cell の exact rewrite -/

namespace AdjacentFerrersSwap

/--
`deltaR` を small inverse quotient へ exact に展開する integer 版。

  3^a deltaR = 2^i + 2^k q_F.
-/
theorem threePow_mul_deltaR_eq_twoPow_add_localQuotient
    (S : AdjacentFerrersSwap) :
    (3 : ℤ) ^ S.fareyLeftExponent * (S.deltaR : ℤ) =
      (2 : ℤ) ^ S.position +
        (2 : ℤ) ^ S.length * (S.fareyLocalQuotient : ℤ) := by
  have h := S.threePow_mul_scaled_fareyLocalInverse_eq
  rw [← S.deltaR_eq_twoPow_mul_fareyLocalInverse] at h
  exact_mod_cast h

/--
Farey residue を `deltaR` と local quotient で exact に展開する。

  D = G - deltaR + 3^r q_F.
-/
theorem fareyResidue_eq_gap_sub_deltaR_add_localQuotient
    (S : AdjacentFerrersSwap) :
    S.toFareyCellPacket.residue =
      S.toFareyCellPacket.G - (S.deltaR : ℤ) +
        (3 : ℤ) ^ S.fareyRightExponent *
          (S.fareyLocalQuotient : ℤ) := by
  have hDeltaNat := S.deltaR_eq_twoPow_mul_fareyLocalInverse
  have hDelta :
      (S.deltaR : ℤ) =
        (2 : ℤ) ^ S.position * (S.fareyLocalInverse : ℤ) := by
    exact_mod_cast hDeltaNat
  have hH := S.fareyH_cast
  unfold FareyCellPacket.residue
  dsimp [AdjacentFerrersSwap.toFareyCellPacket]
  rw [hH]
  unfold AdjacentFerrersSwap.fareyS
  rw [hDelta]
  rw [
    S.length_eq_position_add_fareyTailDepth,
    S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent,
    pow_add,
    pow_add
  ]
  ring

/-- residue identity を local quotient を左にした形で読む。 -/
theorem threePow_right_mul_localQuotient_eq_residue_sub_gap_add_deltaR
    (S : AdjacentFerrersSwap) :
    (3 : ℤ) ^ S.fareyRightExponent *
        (S.fareyLocalQuotient : ℤ) =
      S.toFareyCellPacket.residue -
        S.toFareyCellPacket.G + (S.deltaR : ℤ) := by
  have h := S.fareyResidue_eq_gap_sub_deltaR_add_localQuotient
  linarith

end AdjacentFerrersSwap

namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
#4 の terminal RHS を canonical terminal critical state で名前付けする。
`A.normalForm.terminal + 1 = terminalCriticalStart` により、
`AttachedTerminalPredFusion` の右辺と同じ量である。
-/
noncomputable def terminalCarryRhs
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) : ℤ :=
  let c := P.terminalCriticalStart
  let I := P.criticalizationStart_spec
  let Z :=
    P.integralCriticalTailStateInt
      I c
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  (2 : ℤ) ^ carryRunGap P c A.normalForm.terminal * Z + 2

/-- `AttachedTerminalPredFusion` に現れる RHS と canonical `terminalCarryRhs` は同一。 -/
theorem terminalPred_carry_rhs_eq_terminalCarryRhs
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    let k := A.normalForm.terminal
    let I := P.criticalizationStart_spec
    let ZNext :=
      P.integralCriticalTailStateInt
        I (k + 1)
        (by
          have hCrit := A.criticalization_le_previous
          have hPrevTerm := A.normalForm.previous_lt_terminal
          dsimp [k]
          omega)
        (by
          have hSucc := A.terminal_succ_eq_terminalCriticalStart
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [k]
          omega)
    (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart k * ZNext + 2 =
      A.terminalCarryRhs := by
  dsimp
  unfold terminalCarryRhs
  dsimp
  have hSucc :
      A.normalForm.terminal + 1 = P.terminalCriticalStart :=
    A.terminal_succ_eq_terminalCriticalStart
  simp only [hSucc]

/-- terminal top position は attached terminal predecessor の ordinary checkpoint。 -/
theorem terminalTopCellPosition_eq_terminal_checkpoint
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    P.terminalTopCellPosition =
      profileCheckpoint P.h A.normalForm.terminal := by
  unfold PureBProfileObstruction.terminalTopCellPosition
  unfold PureBProfileObstruction.terminalTopColumn
  unfold profileCheckpoint
  rw [A.terminal_eq]

/--
terminal top position `p` と carry gap `e` は critical roof `beta(c)` を exact に分割する。

  p + e = beta(c).
-/
theorem terminalTopCellPosition_add_carryRunGap_eq_beatty
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    P.terminalTopCellPosition +
        carryRunGap
          P P.terminalCriticalStart A.normalForm.terminal =
      beattyIndex P.terminalCriticalStart := by
  have hSucc := A.terminal_succ_eq_terminalCriticalStart
  have hGap :=
    carryRunGap_of_succ_eq
      P hSucc
  have hPos := A.terminalTopCellPosition_eq_terminal_checkpoint
  have hCheckpointLe :
      profileCheckpoint P.h A.normalForm.terminal ≤
        beattyIndex A.normalForm.terminal := by
    unfold profileCheckpoint
    omega
  have hBetaLe :
      beattyIndex A.normalForm.terminal ≤
        beattyIndex P.terminalCriticalStart := by
    have hlt : A.normalForm.terminal < P.terminalCriticalStart := by
      omega
    exact le_of_lt (beattyIndex_strictMono hlt)
  rw [hGap]
  rw [hPos]
  omega

/--
#4 RHS を terminal-top dyadic position で scale すると、pure prefix と `y-q` に戻る。

  2^p (2^e Z_c + 2)
    = localPrefix(c) + 3^c (y-q) + 2^(p+1).
-/
theorem terminalCarryRhs_scaled_eq_localPrefix_add_y_sub_q
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    (2 : ℤ) ^ P.terminalTopCellPosition * A.terminalCarryRhs =
      P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) +
        (2 : ℤ) ^ (P.terminalTopCellPosition + 1) := by
  let c := P.terminalCriticalStart
  let I := P.criticalizationStart_spec
  let Z :=
    P.integralCriticalTailStateInt
      I c
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  have hState :=
    P.terminalCritical_integralState_scaled_eq_localPrefix_add_y_sub_q
  have hExp := A.terminalTopCellPosition_add_carryRunGap_eq_beatty
  dsimp [c, I, Z] at hState
  unfold terminalCarryRhs
  dsimp
  calc
    (2 : ℤ) ^ P.terminalTopCellPosition *
        ((2 : ℤ) ^
            carryRunGap
              P P.terminalCriticalStart A.normalForm.terminal *
            P.integralCriticalTailStateInt
              P.criticalizationStart_spec
              P.terminalCriticalStart
              P.criticalizationStart_le_terminalCriticalStart
              P.terminalCriticalStart_spec.1 +
          2)
        =
      (2 : ℤ) ^
          (P.terminalTopCellPosition +
            carryRunGap
              P P.terminalCriticalStart A.normalForm.terminal) *
          P.integralCriticalTailStateInt
            P.criticalizationStart_spec
            P.terminalCriticalStart
            P.criticalizationStart_le_terminalCriticalStart
            P.terminalCriticalStart_spec.1 +
        (2 : ℤ) ^ (P.terminalTopCellPosition + 1) := by
          rw [pow_add, pow_succ]
          ring
    _ =
      (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.integralCriticalTailStateInt
            P.criticalizationStart_spec
            P.terminalCriticalStart
            P.criticalizationStart_le_terminalCriticalStart
            P.terminalCriticalStart_spec.1 +
        (2 : ℤ) ^ (P.terminalTopCellPosition + 1) := by
          rw [hExp]
    _ =
      P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) +
        (2 : ℤ) ^ (P.terminalTopCellPosition + 1) := by
          rw [hState]

/--
minimal actual terminal packet を代入すると `y-q` は canonical representative `R` になる。
-/
theorem terminalCarryRhs_scaled_eq_localPrefix_add_representative
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    let P := M.toPureBProfileObstruction hL
    (2 : ℤ) ^ T.step.edge.position * A.terminalCarryRhs =
      P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (3 : ℤ) ^ P.terminalCriticalStart *
          (leastRepresentative M.word : ℤ) +
        (2 : ℤ) ^ (T.step.edge.position + 1) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  have hCore := A.terminalCarryRhs_scaled_eq_localPrefix_add_y_sub_q
  have hRep :=
    M.toPureBProfileObstruction_y_sub_q_eq_leastRepresentative hL
  have hPos := T.position_eq
  rw [← hPos] at hCore
  rw [hRep] at hCore
  exact hCore

/--
`R < deltaR` を exact に差し込んだ #4 RHS の deltaR-clearance normal form。

  2^p RHS
    = localPrefix
      + 2^H q_F
      + 3*2^p
      - 3^c (deltaR-R).

最後の項は terminal minimality packet により strict positive quantity の減算になる。
-/
theorem terminalCarryRhs_scaled_eq_deltaR_clearance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    (2 : ℤ) ^ S.position * A.terminalCarryRhs =
      P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.fareyLocalQuotient : ℤ) +
        3 * (2 : ℤ) ^ S.position -
        (3 : ℤ) ^ P.terminalCriticalStart *
          ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  have hCore :=
    terminalCarryRhs_scaled_eq_localPrefix_add_representative
      M hL A T
  have hDelta := S.threePow_mul_deltaR_eq_twoPow_add_localQuotient
  have hA := T.fareyLeftExponent_eq
  dsimp [P, S] at hCore hDelta hA ⊢
  rw [hA] at hDelta
  rw [pow_succ] at hCore
  calc
    (2 : ℤ) ^ T.step.edge.position * A.terminalCarryRhs
        =
      (M.toPureBProfileObstruction hL).profileAffineLocalPrefixZ
          (M.toPureBProfileObstruction hL).terminalCriticalStart +
        (3 : ℤ) ^
            (M.toPureBProfileObstruction hL).terminalCriticalStart *
          (leastRepresentative M.word : ℤ) +
        2 * (2 : ℤ) ^ T.step.edge.position := by
      simpa [mul_comm] using hCore
    _ =
      (M.toPureBProfileObstruction hL).profileAffineLocalPrefixZ
          (M.toPureBProfileObstruction hL).terminalCriticalStart +
        (2 : ℤ) ^ T.step.edge.length *
          (T.step.edge.fareyLocalQuotient : ℤ) +
        3 * (2 : ℤ) ^ T.step.edge.position -
        (3 : ℤ) ^
            (M.toPureBProfileObstruction hL).terminalCriticalStart *
          ((T.step.edge.deltaR : ℤ) -
            (leastRepresentative M.word : ℤ)) := by
      linear_combination hDelta

/--
terminal Farey packet の residue と deltaR の二つを同時に入れた exact balance。

左辺の追加二項

  2^H (G-D),
  3^m (deltaR-R)

は packet の strict inequalities によりともに正である。
-/
theorem terminalCarryRhs_twoClearance_exact_balance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let D := S.toFareyCellPacket.residue
    let G := S.toFareyCellPacket.G
    let r := S.fareyRightExponent
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) +
      (2 : ℤ) ^ S.length * (G - D) +
      (3 : ℤ) ^ P.m *
        ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) =
      (3 : ℤ) ^ r *
          P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  have hClear :=
    terminalCarryRhs_scaled_eq_deltaR_clearance M hL A T
  have hRes :=
    S.threePow_right_mul_localQuotient_eq_residue_sub_gap_add_deltaR
  have hOdd := S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent
  have hA := T.fareyLeftExponent_eq
  have hM := T.oddTotal_eq
  have hm :
      P.m = P.terminalCriticalStart + S.fareyRightExponent := by
    dsimp [P, S] at hOdd hA hM ⊢
    rw [hM, hA] at hOdd
    exact hOdd
  have hThree :
      (3 : ℤ) ^ P.m =
        (3 : ℤ) ^ P.terminalCriticalStart *
          (3 : ℤ) ^ S.fareyRightExponent := by
    rw [hm, pow_add]
  dsimp [P, S] at hClear hRes hThree ⊢
  rw [hClear, hThree, pow_succ]
  linear_combination
    ((2 : ℤ) ^ T.step.edge.length) * hRes

/-- terminal packet が与える二つの strict clearance。 -/
theorem terminalTop_twoClearances_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    0 < T.step.edge.toFareyCellPacket.G -
        T.step.edge.toFareyCellPacket.residue ∧
      0 < (T.step.edge.deltaR : ℤ) -
        (leastRepresentative M.word : ℤ) := by
  constructor
  · linarith [T.residue_lt_gap]
  · have h := T.R_lt_deltaR
    have hZ :
        (leastRepresentative M.word : ℤ) <
          (T.step.edge.deltaR : ℤ) := by
      exact_mod_cast h
    exact sub_pos.mpr hZ

/--
二つの strict clearance を捨てることで得る、terminal fused RHS の最初の strict upper bound。

まだ右辺に `profileAffineLocalPrefixZ c` が残るため、これ単独では end-smallness ではない。
-/
theorem terminalCarryRhs_strict_lt_farey_prefix_budget
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let r := S.fareyRightExponent
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) <
      (3 : ℤ) ^ r *
          P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  have hBal :=
    terminalCarryRhs_twoClearance_exact_balance M hL A T
  have hPos := terminalTop_twoClearances_pos M hL T
  have hGapPos :
      0 <
        (2 : ℤ) ^ S.length *
          (S.toFareyCellPacket.G - S.toFareyCellPacket.residue) :=
    mul_pos (by positivity) hPos.1
  have hRPos :
      0 <
        (3 : ℤ) ^ P.m *
          ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) :=
    mul_pos (by positivity) hPos.2
  dsimp [P, S] at hBal hGapPos hRPos ⊢
  linarith

end AttachedTwoCornerPacket

end MultiCorner

end CSTMicro
end Collatz2
