import CollatzLean.Collatz2.CSTMicro.CarryGeometry.NormalizedFerrersLedger

set_option linter.style.longLine false
/-!
# General CST: exact lifted Farey cocycle / cell ledger

`NormalizedFerrersCocycle` / `NormalizedFerrersLedger` では
first-passage Ferrers step に対して

* carry    : `Δq = D`
* no-carry : `Δq < 0`

までを保持している。

このファイルでは no-carry 側も canonical Farey data で exact に計算し、

* carry    : `Δq = D`
* no-carry : `Δq = D - G`

を証明する。

したがって一つの step の law は

  Δq = D - G * 1_{no-carry}

で統一できる。

さらに chain 全体で telescope し、

  q_finish - q_start
    = sum(all cell residues D)
      - G * (# no-carry steps)

を exact に得る。

最後に `FirstFailureProvenance` へ適用して

  q_upper
    = q_boundary
      + prefixCellResidueSum
      + D_failure
      - G * prefixNoCarryCount

を公開する。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. no-carry の exact local law -/

namespace AdjacentFerrersSwap

/--
first-passage contracting adjacent cell の no-carry branch では
normalized defect の差は exact に `D - G`。

carry branch の `Δq = D` と合わせると、carry/no-carry の違いは
common terminal gap `G` を一回引くかどうかだけになる。
-/
theorem normalized_upper_eq_lower_add_fareyResidue_sub_gap_of_noCarry
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord)
    (hNoCarry : S.NoCarry) :
    normalizedSeparationDefectInt S.upperWord =
      normalizedSeparationDefectInt S.lowerWord +
        S.toFareyCellPacket.residue -
        S.toFareyCellPacket.G := by
  have hUpperContract : CoefficientContracting S.upperWord := by
    have h := hLowerFP.2.2
    unfold CoefficientContracting at h ⊢
    simpa using h
  have hLowerFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.lowerWord hLowerFP.2.2
  have hUpperFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.upperWord hUpperContract
  rw [S.parityModulus_lowerWord] at hLowerFactor
  rw [S.parityModulus_upperWord] at hUpperFactor
  have hB := S.lower_affineConst_eq_upper_add_deltaB
  have hR := S.upperR_eq_add_of_noCarry hNoCarry
  have hBz :
      (affineConst S.lowerWord : ℤ) =
        (affineConst S.upperWord : ℤ) + (S.deltaB : ℤ) := by
    exact_mod_cast hB
  have hRz :
      (S.upperR : ℤ) =
        (S.lowerR : ℤ) + (S.deltaR : ℤ) := by
    exact_mod_cast hR
  have hG :=
    S.fareyPacket_G_eq_wordTerminalGap hLowerFP.2.2
  have hJump :=
    S.carryCellJumpInt_eq_modulus_mul_fareyResidue
      hLowerFP.2.2
  have hCompNat :
      S.carryComplement + S.deltaR = S.modulus := by
    unfold AdjacentFerrersSwap.carryComplement
    exact Nat.sub_add_cancel (Nat.le_of_lt S.deltaR_lt_modulus)
  have hComp :
      (S.carryComplement : ℤ) + (S.deltaR : ℤ) =
        (S.modulus : ℤ) := by
    exact_mod_cast hCompNat
  unfold AdjacentFerrersSwap.carryCellJumpInt at hJump
  rw [← hG] at hJump
  have hDefDiff :
      wordSeparationDefectInt S.upperWord -
          wordSeparationDefectInt S.lowerWord =
        (S.modulus : ℤ) *
          (S.toFareyCellPacket.residue -
            S.toFareyCellPacket.G) := by
    unfold wordSeparationDefectInt
    change
      ((affineConst S.upperWord : ℤ) -
          (wordTerminalGap S.upperWord : ℤ) * (S.upperR : ℤ)) -
        ((affineConst S.lowerWord : ℤ) -
          (wordTerminalGap S.lowerWord : ℤ) * (S.lowerR : ℤ)) =
      (S.modulus : ℤ) *
        (S.toFareyCellPacket.residue -
          S.toFareyCellPacket.G)
    rw [← S.wordTerminalGap_eq]
    rw [hBz, hRz, ← hG]
    linear_combination
      hJump - S.toFareyCellPacket.G * hComp
  rw [hUpperFactor, hLowerFactor] at hDefDiff
  have hModPos : 0 < (S.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  nlinarith

end AdjacentFerrersSwap

namespace FerrersStep

/-- FerrersStep 版の exact no-carry law `Δq = D - G`。 -/
theorem normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hNoCarry : S.edge.NoCarry) :
    normalizedStepDelta lower upper =
      S.edge.toFareyCellPacket.residue -
        S.edge.toFareyCellPacket.G := by
  have hEdgeFP : IsFirstPassageWord S.edge.lowerWord := by
    simpa [S.lower_eq] using hLowerFP
  have h :=
    S.edge.normalized_upper_eq_lower_add_fareyResidue_sub_gap_of_noCarry
      hEdgeFP hNoCarry
  have hLower :
      normalizedSeparationDefectInt lower =
        normalizedSeparationDefectInt S.edge.lowerWord :=
    congrArg normalizedSeparationDefectInt S.lower_eq
  have hUpper :
      normalizedSeparationDefectInt upper =
        normalizedSeparationDefectInt S.edge.upperWord :=
    congrArg normalizedSeparationDefectInt S.upper_eq
  unfold normalizedStepDelta
  rw [hLower, hUpper]
  linarith

/--
既存 no-carry loss は exact に `G-D`。

従来の「strict positive loss」を canonical Farey residue で完全に同定する。
-/
theorem normalizedNoCarryLoss_eq_gap_sub_fareyResidue_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hNoCarry : S.edge.NoCarry) :
    S.normalizedNoCarryLoss =
      S.edge.toFareyCellPacket.G -
        S.edge.toFareyCellPacket.residue := by
  rw [S.normalizedNoCarryLoss_eq_neg_delta_of_noCarry hNoCarry]
  rw [S.normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
        hLowerFP hNoCarry]
  ring

/-- no-carry first-passage cell では canonical residue は `G` より strict に小さい。 -/
theorem fareyResidue_lt_gap_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hNoCarry : S.edge.NoCarry) :
    S.edge.toFareyCellPacket.residue <
      S.edge.toFareyCellPacket.G := by
  have hLoss :=
    S.normalizedNoCarryLoss_pos_of_noCarry hLowerFP hNoCarry
  rw [S.normalizedNoCarryLoss_eq_gap_sub_fareyResidue_of_noCarry
        hLowerFP hNoCarry] at hLoss
  linarith

/-- 一 step が no-carry なら 1、carry なら 0 を返す exact lift indicator。 -/
noncomputable def normalizedNoCarryIndicator
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ := by
  classical
  exact if S.edge.NoCarry then 1 else 0

/-- no-carry step の indicator は 1。 -/
theorem normalizedNoCarryIndicator_eq_one_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hNoCarry : S.edge.NoCarry) :
    S.normalizedNoCarryIndicator = 1 := by
  classical
  unfold normalizedNoCarryIndicator
  rw [ite_eq_left hNoCarry]

/-- carry step の indicator は 0。 -/
theorem normalizedNoCarryIndicator_eq_zero_of_hasCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hCarry : S.edge.HasCarry) :
    S.normalizedNoCarryIndicator = 0 := by
  classical
  unfold normalizedNoCarryIndicator
  rw [ite_eq_right (S.edge.not_noCarry_of_hasCarry hCarry)]

/--
一つの first-passage Ferrers step の exact lifted Farey law。

  Δq = D - G * 1_{no-carry}.
-/
theorem normalizedStepDelta_eq_residue_sub_gap_mul_noCarryIndicator
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    normalizedStepDelta lower upper =
      S.edge.toFareyCellPacket.residue -
        S.edge.toFareyCellPacket.G *
          (S.normalizedNoCarryIndicator : ℤ) := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · rw [S.normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
          hLowerFP hNo]
    rw [S.normalizedNoCarryIndicator_eq_one_of_noCarry hNo]
    norm_num
  · rw [S.normalizedStepDelta_eq_fareyResidue_of_hasCarry
          hLowerFP hCarry]
    rw [S.normalizedNoCarryIndicator_eq_zero_of_hasCarry hCarry]
    ring

end FerrersStep

/-! ## 2. chain-level exact cell ledger -/

namespace FerrersChain

/-- chain が通過する全 Ferrers cell の canonical Farey residue の総和。 -/
noncomputable def normalizedCellResidueSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℤ
  | .refl _ => 0
  | .step C S =>
      C.normalizedCellResidueSum +
        S.edge.toFareyCellPacket.residue

/-- chain に現れる no-carry step の個数。 -/
noncomputable def normalizedNoCarryCount
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S =>
      C.normalizedNoCarryCount +
        S.normalizedNoCarryIndicator

/-- Ferrers chain は word-level terminal gap も保存する。 -/
theorem wordTerminalGap_eq
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    wordTerminalGap start = wordTerminalGap finish := by
  unfold wordTerminalGap
  rw [C.length_eq, C.oddCount_eq]

/--
first-passage Ferrers chain の exact cell ledger。

  q_finish
    = q_start
      + sum(all D)
      - G * (# no-carry).

ここで `G = wordTerminalGap start` は chain 全体で共通。
-/
theorem normalized_finish_eq_start_add_cellResidueSum_sub_gap_mul_noCarryCount
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    normalizedSeparationDefectInt finish =
      normalizedSeparationDefectInt start +
        C.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C.normalizedNoCarryCount : ℤ) := by
  induction C with
  | refl =>
      simp [normalizedCellResidueSum, normalizedNoCarryCount]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hStep :=
        S.normalizedStepDelta_eq_residue_sub_gap_mul_noCarryIndicator
          hUFP
      have hStepEndpoint :
          normalizedSeparationDefectInt v =
            normalizedSeparationDefectInt u +
              FerrersStep.normalizedStepDelta u v := by
        unfold FerrersStep.normalizedStepDelta
        ring
      have hEdgeFP : IsFirstPassageWord S.edge.lowerWord := by
        simpa [S.lower_eq] using hUFP
      have hGEdge :=
        S.edge.fareyPacket_G_eq_wordTerminalGap hEdgeFP.2.2
      have hGStart :
          S.edge.toFareyCellPacket.G =
            (wordTerminalGap start : ℤ) := by
        calc
          S.edge.toFareyCellPacket.G
              = (wordTerminalGap S.edge.lowerWord : ℤ) :=
                hGEdge
          _ = (wordTerminalGap u : ℤ) := by
                rw [← S.lower_eq]
          _ = (wordTerminalGap start : ℤ) := by
                exact_mod_cast C.wordTerminalGap_eq.symm
      change
        normalizedSeparationDefectInt v =
          normalizedSeparationDefectInt start +
            (C.normalizedCellResidueSum +
              S.edge.toFareyCellPacket.residue) -
            (wordTerminalGap start : ℤ) *
              ((C.normalizedNoCarryCount +
                S.normalizedNoCarryIndicator : ℕ) : ℤ)
      calc
        normalizedSeparationDefectInt v
            = normalizedSeparationDefectInt u +
                FerrersStep.normalizedStepDelta u v :=
          hStepEndpoint
        _ = normalizedSeparationDefectInt u +
              (S.edge.toFareyCellPacket.residue -
                S.edge.toFareyCellPacket.G *
                  (S.normalizedNoCarryIndicator : ℤ)) := by
            rw [hStep]
        _ =
            (normalizedSeparationDefectInt start +
                C.normalizedCellResidueSum -
                (wordTerminalGap start : ℤ) *
                  (C.normalizedNoCarryCount : ℤ)) +
              (S.edge.toFareyCellPacket.residue -
                S.edge.toFareyCellPacket.G *
                  (S.normalizedNoCarryIndicator : ℤ)) := by
            rw [ih]
        _ =
            normalizedSeparationDefectInt start +
              (C.normalizedCellResidueSum +
                S.edge.toFareyCellPacket.residue) -
              (wordTerminalGap start : ℤ) *
                ((C.normalizedNoCarryCount +
                  S.normalizedNoCarryIndicator : ℕ) : ℤ) := by
            rw [hGStart]
            push_cast
            ring

/--
endpoint 差 `normalizedDelta` の exact cell-sum form。

  normalizedDelta
    = sum(all D) - G * (# no-carry).
-/
theorem normalizedDelta_eq_cellResidueSum_sub_gap_mul_noCarryCount
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C.normalizedDelta =
      C.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C.normalizedNoCarryCount : ℤ) := by
  have hEndpoint := C.normalized_finish_eq_start_add_delta
  have hCells :=
    C.normalized_finish_eq_start_add_cellResidueSum_sub_gap_mul_noCarryCount
      hStartFP
  linarith

/--
既存 carry/no-carry ledger と exact cell ledger は同じ cocycle の二表示。
-/
theorem normalizedCarryContribution_sub_noCarryLoss_eq_cellResidueSum_sub_gap_mul_noCarryCount
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C.normalizedCarryContribution -
        C.normalizedNoCarryLoss =
      C.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C.normalizedNoCarryCount : ℤ) := by
  have hOld :=
    C.normalizedDelta_eq_carryContribution_sub_noCarryLoss
      hStartFP
  have hNew :=
    C.normalizedDelta_eq_cellResidueSum_sub_gap_mul_noCarryCount
      hStartFP
  linarith

end FerrersChain

/-! ## 3. A boundary -> B first failure の exact cell ledger -/

namespace FirstFailureProvenance

/-- boundary から first-failure lower までに通過した全 cell residue の総和。 -/
noncomputable def prefixCellResidueSum
    {target : ParityWord}
    (P : FirstFailureProvenance target) : ℤ :=
  P.safePrefixChain.toFerrersChain.normalizedCellResidueSum

/-- boundary から first-failure lower までに起きた no-carry step の個数。 -/
noncomputable def prefixNoCarryCount
    {target : ParityWord}
    (P : FirstFailureProvenance target) : ℕ :=
  P.safePrefixChain.toFerrersChain.normalizedNoCarryCount

/-- safe prefix lower の exact cell ledger。 -/
theorem lower_eq_boundary_add_prefixCellResidueSum_sub_gap_mul_prefixNoCarryCount
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.lower =
      normalizedSeparationDefectInt P.boundary +
        P.prefixCellResidueSum -
        (wordTerminalGap P.boundary : ℤ) *
          (P.prefixNoCarryCount : ℤ) := by
  have h :=
    FerrersChain.normalized_finish_eq_start_add_cellResidueSum_sub_gap_mul_noCarryCount
      P.safePrefixChain.toFerrersChain
      P.boundary_isBoundary.1
  simpa [prefixCellResidueSum, prefixNoCarryCount] using h

/-- final failure cell の Farey `G` は boundary から保存された common terminal gap。 -/
theorem failureGap_eq_boundaryTerminalGap
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.failureStep.edge.toFareyCellPacket.G =
      (wordTerminalGap P.boundary : ℤ) := by
  have hEdgeFP :
      IsFirstPassageWord P.failureStep.edge.lowerWord := by
    simpa [P.failureStep.lower_eq] using P.lower_firstPassage
  have hG :=
    P.failureStep.edge.fareyPacket_G_eq_wordTerminalGap
      hEdgeFP.2.2
  have hPrefixGap :=
    P.safePrefixChain.toFerrersChain.wordTerminalGap_eq
  calc
    P.failureStep.edge.toFareyCellPacket.G
        = (wordTerminalGap P.failureStep.edge.lowerWord : ℤ) :=
      hG
    _ = (wordTerminalGap P.lower : ℤ) := by
      rw [← P.failureStep.lower_eq]
    _ = (wordTerminalGap P.boundary : ℤ) := by
      exact_mod_cast hPrefixGap.symm

/--
A boundary から B first-failure upper までの exact lifted cell cocycle。

  q_upper
    = q_boundary
      + prefixCellResidueSum
      + D_failure
      - G * prefixNoCarryCount.
-/
theorem upper_eq_boundary_add_prefixCellResidueSum_add_failureResidue_sub_gap_mul_prefixNoCarryCount
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.upper =
      normalizedSeparationDefectInt P.boundary +
        P.prefixCellResidueSum +
        P.failureStep.edge.toFareyCellPacket.residue -
        P.failureStep.edge.toFareyCellPacket.G *
          (P.prefixNoCarryCount : ℤ) := by
  calc
    normalizedSeparationDefectInt P.upper
        = normalizedSeparationDefectInt P.lower +
            P.failureStep.edge.toFareyCellPacket.residue :=
      P.upper_eq_lower_add_failureResidue
    _ =
        (normalizedSeparationDefectInt P.boundary +
            P.prefixCellResidueSum -
            (wordTerminalGap P.boundary : ℤ) *
              (P.prefixNoCarryCount : ℤ)) +
          P.failureStep.edge.toFareyCellPacket.residue := by
      rw [P.lower_eq_boundary_add_prefixCellResidueSum_sub_gap_mul_prefixNoCarryCount]
    _ =
        normalizedSeparationDefectInt P.boundary +
          P.prefixCellResidueSum +
          P.failureStep.edge.toFareyCellPacket.residue -
          P.failureStep.edge.toFareyCellPacket.G *
            (P.prefixNoCarryCount : ℤ) := by
      rw [P.failureGap_eq_boundaryTerminalGap]
      ring

/--
first failure が zero を跨ぐための exact cell-budget necessary condition。

boundary safety と no-carry ごとの full-gap penalty を、
全 prefix cell residue と final failure residue が補わなければならない。
-/
theorem boundarySafety_add_gap_mul_prefixNoCarryCount_le_prefixCellResidueSum_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    - normalizedSeparationDefectInt P.boundary +
        P.failureStep.edge.toFareyCellPacket.G *
          (P.prefixNoCarryCount : ℤ) ≤
      P.prefixCellResidueSum +
        P.failureStep.edge.toFareyCellPacket.residue := by
  have hUpper := P.upper_normalized_nonneg
  have hEq :=
    P.upper_eq_boundary_add_prefixCellResidueSum_add_failureResidue_sub_gap_mul_prefixNoCarryCount
  linarith

/--
A -> B exact lifted cell ledger の中心 packet。
-/
theorem boundary_to_firstFailure_exactCellLedger_packet
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.boundary ≤ -1 ∧
      normalizedSeparationDefectInt P.lower < 0 ∧
      0 ≤ normalizedSeparationDefectInt P.upper ∧
      normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.boundary +
          P.prefixCellResidueSum +
          P.failureStep.edge.toFareyCellPacket.residue -
          P.failureStep.edge.toFareyCellPacket.G *
            (P.prefixNoCarryCount : ℤ) ∧
      - normalizedSeparationDefectInt P.boundary +
          P.failureStep.edge.toFareyCellPacket.G *
            (P.prefixNoCarryCount : ℤ) ≤
        P.prefixCellResidueSum +
          P.failureStep.edge.toFareyCellPacket.residue ∧
      0 < P.failureStep.edge.toFareyCellPacket.residue := by
  exact
    ⟨P.boundary_normalized_le_neg_one,
      P.lower_normalized_neg,
      P.upper_normalized_nonneg,
      P.upper_eq_boundary_add_prefixCellResidueSum_add_failureResidue_sub_gap_mul_prefixNoCarryCount,
      P.boundarySafety_add_gap_mul_prefixNoCarryCount_le_prefixCellResidueSum_add_failureResidue,
      P.failureResidue_pos⟩

end FirstFailureProvenance

end CSTMicro
end Collatz2
