import CollatzLean.Collatz2.CSTMicro.CarryGeometry.NormalizedFerrersCocycle

/-!
# General CST: carry / no-carry ledger for the normalized Ferrers cocycle

`NormalizedFerrersCocycle` では一つの first-passage Ferrers step に対して

  no-carry : delta q < 0
  carry    : delta q = canonical Farey residue

を得た。

このファイルではその局所法則を chain 全体で実際に会計する。

重要な点として、generic carry residue は first-failure residue と違って
正とは限らない。したがって

* carry contribution は residue の符号付き総和
* no-carry contribution だけを正の loss として分離

し、

  q_finish
    = q_start + carryContribution - noCarryLoss

を exact に証明する。

最後に `FirstFailureProvenance` へ適用し、

  q_upper
    = q_boundary
      + prefixCarryContribution
      - prefixNoCarryLoss
      + failureResidue

および

  -q_boundary + prefixNoCarryLoss
    <= prefixCarryContribution + failureResidue

を得る。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. carry / no-carry の排反 -/

namespace AdjacentFerrersSwap

/-- no-carry なら carry ではない。 -/
theorem not_hasCarry_of_noCarry
    (S : AdjacentFerrersSwap)
    (hNo : S.NoCarry) :
    ¬ S.HasCarry := by
  intro hCarry
  unfold NoCarry at hNo
  unfold HasCarry at hCarry
  omega

/-- carry なら no-carry ではない。 -/
theorem not_noCarry_of_hasCarry
    (S : AdjacentFerrersSwap)
    (hCarry : S.HasCarry) :
    ¬ S.NoCarry := by
  intro hNo
  unfold HasCarry at hCarry
  unfold NoCarry at hNo
  omega

end AdjacentFerrersSwap

/-! ## 2. 一つの Ferrers step の ledger entry -/

namespace FerrersStep

/--
一つの step の carry contribution。

carry なら canonical Farey residue、no-carry なら zero。
generic carry residue の符号は固定しない。
-/
noncomputable def normalizedCarryContribution
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℤ := by
  classical
  exact
    if S.edge.HasCarry then
      S.edge.toFareyCellPacket.residue
    else
      0

/--
一つの step の no-carry loss。

no-carry では `delta q < 0` なので `- delta q` を loss とし、
carry では zero とする。
-/
noncomputable def normalizedNoCarryLoss
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℤ := by
  classical
  exact
    if S.edge.NoCarry then
      - normalizedStepDelta lower upper
    else
      0

/-- no-carry step の carry contribution は zero。 -/
theorem normalizedCarryContribution_eq_zero_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hNo : S.edge.NoCarry) :
    S.normalizedCarryContribution = 0 := by
  classical
  unfold normalizedCarryContribution
  rw [if_neg (S.edge.not_hasCarry_of_noCarry hNo)]

/-- carry step の carry contribution は canonical Farey residue。 -/
theorem normalizedCarryContribution_eq_fareyResidue_of_hasCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hCarry : S.edge.HasCarry) :
    S.normalizedCarryContribution =
      S.edge.toFareyCellPacket.residue := by
  classical
  unfold normalizedCarryContribution
  rw [if_pos hCarry]

/-- no-carry step の loss は `- delta q`。 -/
theorem normalizedNoCarryLoss_eq_neg_delta_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hNo : S.edge.NoCarry) :
    S.normalizedNoCarryLoss =
      - normalizedStepDelta lower upper := by
  classical
  unfold normalizedNoCarryLoss
  rw [if_pos hNo]

/-- carry step の no-carry loss は zero。 -/
theorem normalizedNoCarryLoss_eq_zero_of_hasCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hCarry : S.edge.HasCarry) :
    S.normalizedNoCarryLoss = 0 := by
  classical
  unfold normalizedNoCarryLoss
  rw [if_neg (S.edge.not_noCarry_of_hasCarry hCarry)]

/--
一つの first-passage Ferrers step の exact ledger law。

  delta q = carryContribution - noCarryLoss.
-/
theorem normalizedStepDelta_eq_carryContribution_sub_noCarryLoss
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    normalizedStepDelta lower upper =
      S.normalizedCarryContribution -
        S.normalizedNoCarryLoss := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · have hCarryZero :=
      S.normalizedCarryContribution_eq_zero_of_noCarry hNo
    have hLoss :=
      S.normalizedNoCarryLoss_eq_neg_delta_of_noCarry hNo
    rw [hCarryZero, hLoss]
    ring
  · have hCarryEq :=
      S.normalizedCarryContribution_eq_fareyResidue_of_hasCarry hCarry
    have hLossZero :=
      S.normalizedNoCarryLoss_eq_zero_of_hasCarry hCarry
    have hDelta :=
      S.normalizedStepDelta_eq_fareyResidue_of_hasCarry
        hLowerFP hCarry
    rw [hDelta, hCarryEq, hLossZero]
    ring

/-- first-passage step の no-carry loss は nonnegative。 -/
theorem normalizedNoCarryLoss_nonneg
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    0 ≤ S.normalizedNoCarryLoss := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · have hLoss :=
      S.normalizedNoCarryLoss_eq_neg_delta_of_noCarry hNo
    have hDelta :=
      S.normalizedStepDelta_neg_of_noCarry
        hLowerFP hNo
    rw [hLoss]
    omega
  · rw [S.normalizedNoCarryLoss_eq_zero_of_hasCarry hCarry]

/-- actual no-carry step では loss は strict positive。 -/
theorem normalizedNoCarryLoss_pos_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hNo : S.edge.NoCarry) :
    0 < S.normalizedNoCarryLoss := by
  have hLoss :=
    S.normalizedNoCarryLoss_eq_neg_delta_of_noCarry hNo
  have hDelta :=
    S.normalizedStepDelta_neg_of_noCarry
      hLowerFP hNo
  rw [hLoss]
  omega

end FerrersStep

/-! ## 3. Ferrers chain 全体の ledger -/

namespace FerrersChain

/-- chain に現れる carry cell の canonical residue の符号付き総和。 -/
noncomputable def normalizedCarryContribution
    {start finish : ParityWord} :
    FerrersChain start finish → ℤ
  | .refl _ => 0
  | .step C S =>
      C.normalizedCarryContribution +
        S.normalizedCarryContribution

/-- chain に現れる no-carry loss の総和。 -/
noncomputable def normalizedNoCarryLoss
    {start finish : ParityWord} :
    FerrersChain start finish → ℤ
  | .refl _ => 0
  | .step C S =>
      C.normalizedNoCarryLoss +
        S.normalizedNoCarryLoss

/--
first-passage Ferrers chain の exact carry/no-carry ledger。

  q_finish
    = q_start
      + carryContribution
      - noCarryLoss.
-/
theorem normalized_finish_eq_start_add_carryContribution_sub_noCarryLoss
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    normalizedSeparationDefectInt finish =
      normalizedSeparationDefectInt start +
        C.normalizedCarryContribution -
        C.normalizedNoCarryLoss := by
  induction C with
  | refl =>
      simp [normalizedCarryContribution, normalizedNoCarryLoss]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hStep :=
        S.normalizedStepDelta_eq_carryContribution_sub_noCarryLoss
          hUFP
      have hStepEndpoint :
          normalizedSeparationDefectInt v =
            normalizedSeparationDefectInt u +
              FerrersStep.normalizedStepDelta u v := by
        unfold FerrersStep.normalizedStepDelta
        ring
      change
        normalizedSeparationDefectInt v =
          normalizedSeparationDefectInt start +
            (C.normalizedCarryContribution +
              S.normalizedCarryContribution) -
            (C.normalizedNoCarryLoss +
              S.normalizedNoCarryLoss)
      calc
        normalizedSeparationDefectInt v
            =
          normalizedSeparationDefectInt u +
            FerrersStep.normalizedStepDelta u v :=
              hStepEndpoint
        _ =
          normalizedSeparationDefectInt u +
            (S.normalizedCarryContribution -
              S.normalizedNoCarryLoss) := by
                rw [hStep]
        _ =
          (normalizedSeparationDefectInt start +
              C.normalizedCarryContribution -
              C.normalizedNoCarryLoss) +
            (S.normalizedCarryContribution -
              S.normalizedNoCarryLoss) := by
                rw [ih]
        _ =
          normalizedSeparationDefectInt start +
            (C.normalizedCarryContribution +
              S.normalizedCarryContribution) -
            (C.normalizedNoCarryLoss +
              S.normalizedNoCarryLoss) := by
                ring

/-- first-passage chain の accumulated no-carry loss は nonnegative。 -/
theorem normalizedNoCarryLoss_nonneg
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    0 ≤ C.normalizedNoCarryLoss := by
  induction C with
  | refl =>
      simp [normalizedNoCarryLoss]
  | @step u v w C ih =>
      have hUFP : IsFirstPassageWord u :=
        w.preserves_firstPassage hStartFP
      have hStepLoss :=
        C.normalizedNoCarryLoss_nonneg hUFP
      change
        0 ≤ w.normalizedNoCarryLoss +
          C.normalizedNoCarryLoss
      exact add_nonneg ih hStepLoss

/--
endpoint 差として定義された既存 `normalizedDelta` を
actual ledger へ展開する。

  normalizedDelta
    = carryContribution - noCarryLoss.
-/
theorem normalizedDelta_eq_carryContribution_sub_noCarryLoss
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C.normalizedDelta =
      C.normalizedCarryContribution -
        C.normalizedNoCarryLoss := by
  have hEndpoint :=
    C.normalized_finish_eq_start_add_delta
  have hLedger :=
    C.normalized_finish_eq_start_add_carryContribution_sub_noCarryLoss
      hStartFP
  linarith

end FerrersChain

/-! ## 4. provenance の safe prefix ledger -/

namespace FirstFailureProvenance

/-- boundary から first failure lower までの carry residue 符号付き総和。 -/
noncomputable def prefixCarryContribution
    {target : ParityWord}
    (P : FirstFailureProvenance target) : ℤ :=
  P.safePrefixChain.toFerrersChain.normalizedCarryContribution

/-- boundary から first failure lower までの accumulated no-carry loss。 -/
noncomputable def prefixNoCarryLoss
    {target : ParityWord}
    (P : FirstFailureProvenance target) : ℤ :=
  P.safePrefixChain.toFerrersChain.normalizedNoCarryLoss

/-- safe prefix の exact carry/no-carry ledger。 -/
theorem lower_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.lower =
      normalizedSeparationDefectInt P.boundary +
        P.prefixCarryContribution -
        P.prefixNoCarryLoss := by
  have h :=
    FerrersChain.normalized_finish_eq_start_add_carryContribution_sub_noCarryLoss
      P.safePrefixChain.toFerrersChain
      P.boundary_isBoundary.1
  simpa [prefixCarryContribution, prefixNoCarryLoss] using h

/-- safe prefix の no-carry loss は nonnegative。 -/
theorem prefixNoCarryLoss_nonneg
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    0 ≤ P.prefixNoCarryLoss := by
  have h :=
    FerrersChain.normalizedNoCarryLoss_nonneg
      P.safePrefixChain.toFerrersChain
      P.boundary_isBoundary.1
  simpa [prefixNoCarryLoss] using h

/--
A boundary から B first-failure upper までの exact ledger。

  q_upper
    = q_boundary
      + prefixCarryContribution
      - prefixNoCarryLoss
      + D_failure.
-/
theorem upper_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.upper =
      normalizedSeparationDefectInt P.boundary +
        P.prefixCarryContribution -
        P.prefixNoCarryLoss +
        P.failureStep.edge.toFareyCellPacket.residue := by
  calc
    normalizedSeparationDefectInt P.upper
        =
      normalizedSeparationDefectInt P.lower +
        P.failureStep.edge.toFareyCellPacket.residue :=
          P.upper_eq_lower_add_failureResidue
    _ =
      (normalizedSeparationDefectInt P.boundary +
          P.prefixCarryContribution -
          P.prefixNoCarryLoss) +
        P.failureStep.edge.toFareyCellPacket.residue := by
          rw [
            P.lower_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss
          ]
    _ =
      normalizedSeparationDefectInt P.boundary +
        P.prefixCarryContribution -
        P.prefixNoCarryLoss +
        P.failureStep.edge.toFareyCellPacket.residue := by
          ring

/--
first failure を起こすには、
boundary の negative safety と accumulated no-carry loss を
carry residue 群が少なくとも打ち消さなければならない。
-/
theorem boundarySafety_add_noCarryLoss_le_prefixCarry_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    - normalizedSeparationDefectInt P.boundary +
        P.prefixNoCarryLoss ≤
      P.prefixCarryContribution +
        P.failureStep.edge.toFareyCellPacket.residue := by
  have hUpper := P.upper_normalized_nonneg
  have hEq :=
    P.upper_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss_add_failureResidue
  linarith

/--
A boundary は少なくとも one unit negative で no-carry loss は nonnegative なので、
first failure までの carry contribution と final failure residue の和は
少なくとも one。
-/
theorem one_le_prefixCarryContribution_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    1 ≤
      P.prefixCarryContribution +
        P.failureStep.edge.toFareyCellPacket.residue := by
  have hBoundary := P.boundary_normalized_le_neg_one
  have hLoss := P.prefixNoCarryLoss_nonneg
  have hBudget :=
    P.boundarySafety_add_noCarryLoss_le_prefixCarry_add_failureResidue
  linarith

/--
A -> B の chain-level ledger packet。

generic previous carry は符号付きで保持し、
no-carry loss だけを nonnegative quantity として分離する。
-/
theorem boundary_to_firstFailure_ledger_packet
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.boundary ≤ -1 ∧
      0 ≤ P.prefixNoCarryLoss ∧
      normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.boundary +
          P.prefixCarryContribution -
          P.prefixNoCarryLoss +
          P.failureStep.edge.toFareyCellPacket.residue ∧
      - normalizedSeparationDefectInt P.boundary +
          P.prefixNoCarryLoss ≤
        P.prefixCarryContribution +
          P.failureStep.edge.toFareyCellPacket.residue ∧
      1 ≤
        P.prefixCarryContribution +
          P.failureStep.edge.toFareyCellPacket.residue ∧
      0 < P.failureStep.edge.toFareyCellPacket.residue := by
  exact
    ⟨P.boundary_normalized_le_neg_one,
      P.prefixNoCarryLoss_nonneg,
      P.upper_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss_add_failureResidue,
      P.boundarySafety_add_noCarryLoss_le_prefixCarry_add_failureResidue,
      P.one_le_prefixCarryContribution_add_failureResidue,
      P.failureResidue_pos⟩

end FirstFailureProvenance

end CSTMicro
end Collatz2
