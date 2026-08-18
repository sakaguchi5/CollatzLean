import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersCellResiduePotential
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ActualABExactCellLedger

set_option linter.style.longLine false

/-!
# Safe-prefix exact-cell first-passage barrier

`FirstFailureProvenance.safePrefixChain` は boundary から first-failure lower まで
全 endpoint が `WordPureSeparation` を満たすことを data として保持する。

このファイルでは、その「最後まで safe だった」という情報を endpoint total だけでなく
全 intermediate safe endpoint に使える exact inequality にする。

任意の safe reachable endpoint `mid` と、boundary からそこへ至る Ferrers chain `C` に対し

  q(mid)
    = q(boundary)
      + cellResidueSum(C)
      - G * noCarryCount(C)
    < 0.

したがって

  cellResidueSum(C) - G * noCarryCount(C)
    < -q(boundary).

first failure では最後の distinguished carry residue `D_failure` を加えた瞬間だけ
nonnegative side へ入り、

  q(lower) < 0 <= q(upper),
  q(upper) = q(lower) + D_failure

となる。

`FerrersCellResiduePotential` により integer cell sum と no-carry count は endpoints だけで
決まるため、この barrier は chain の選び方に依存しない。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. generic safe reachable endpoint barrier -/

namespace FerrersChain

/--
first-passage start から safe endpoint へ至る任意の Ferrers chain は、
exact cell ledger と strict negative endpoint を同時に持つ。
-/
theorem safe_finish_exact_cell_ledger_and_negative
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hFinishSafe : WordPureSeparation finish) :
    normalizedSeparationDefectInt finish =
        normalizedSeparationDefectInt start +
          C.normalizedCellResidueSum -
          (wordTerminalGap start : ℤ) *
            (C.normalizedNoCarryCount : ℤ)
      ∧
    normalizedSeparationDefectInt finish < 0 := by
  constructor
  · exact
      C.normalized_finish_eq_start_add_cellResidueSum_sub_gap_mul_noCarryCount
        hStartFP
  · have hFinishFP : IsFirstPassageWord finish :=
      C.preserves_firstPassage hStartFP
    exact
      normalizedSeparationDefectInt_neg_of_wordPureSeparation
        hFinishFP hFinishSafe

/--
全 safe reachable endpoint に対する exact first-passage barrier。

  cellResidueSum - G * noCarryCount < -q_start.
-/
theorem safe_finish_cell_ledger_lt_neg_start
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hFinishSafe : WordPureSeparation finish) :
    C.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C.normalizedNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt start := by
  rcases
      C.safe_finish_exact_cell_ledger_and_negative
        hStartFP hFinishSafe with
    ⟨hEq, hNeg⟩
  linarith

/--
同じ safe endpoint なら barrier の left side は chain に依存しない。
-/
theorem safe_finish_cell_ledger_value_chain_independent
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C₁.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C₁.normalizedNoCarryCount : ℤ) =
      C₂.normalizedCellResidueSum -
        (wordTerminalGap start : ℤ) *
          (C₂.normalizedNoCarryCount : ℤ) := by
  have hSum := C₁.normalizedCellResidueSum_chain_independent C₂
  have hCount := C₁.normalizedNoCarryCount_chain_independent C₂ hStartFP
  rw [hSum, hCount]

end FerrersChain

/-! ## 2. provenance boundary から任意の safe intermediate endpoint -/

namespace FirstFailureProvenance

/--
provenance boundary から到達可能な任意の safe endpoint は exact negative barrier 内にある。

これは distinguished `safePrefixChain` の実際の intermediate endpoint 全てに適用できるが、
statement 自体はさらに強く、同じ boundary から Ferrers-reachable な任意の safe word を許す。
-/
theorem every_safe_reachable_endpoint_exact_cell_barrier
    {target mid : ParityWord}
    (P : FirstFailureProvenance target)
    (C : FerrersChain P.boundary mid)
    (hMidSafe : WordPureSeparation mid) :
    normalizedSeparationDefectInt mid =
        normalizedSeparationDefectInt P.boundary +
          C.normalizedCellResidueSum -
          (wordTerminalGap P.boundary : ℤ) *
            (C.normalizedNoCarryCount : ℤ)
      ∧
    normalizedSeparationDefectInt mid < 0
      ∧
    C.normalizedCellResidueSum -
        (wordTerminalGap P.boundary : ℤ) *
          (C.normalizedNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt P.boundary := by
  have hPacket :=
    C.safe_finish_exact_cell_ledger_and_negative
      P.boundary_isBoundary.1 hMidSafe
  have hBarrier :=
    C.safe_finish_cell_ledger_lt_neg_start
      P.boundary_isBoundary.1 hMidSafe
  exact ⟨hPacket.1, hPacket.2, hBarrier⟩

/-- first-failure lower 自身も全-prefix barrier の最後の strict-negative endpoint。 -/
theorem lower_exact_cell_barrier
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.prefixCellResidueSum -
        P.failureStep.edge.toFareyCellPacket.G *
          (P.prefixNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt P.boundary := by
  have hLower := P.lower_normalized_neg
  have hEq :=
    P.lower_eq_boundary_add_prefixCellResidueSum_sub_gap_mul_prefixNoCarryCount
  have hGap := P.failureGap_eq_boundaryTerminalGap
  rw [← hGap] at hEq
  linarith

/--
最後の distinguished failure carry を加える直前 / 直後の exact first crossing。
-/
theorem final_cell_first_crossing
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.lower < 0
      ∧
    0 ≤ normalizedSeparationDefectInt P.upper
      ∧
    normalizedSeparationDefectInt P.upper =
      normalizedSeparationDefectInt P.lower +
        P.failureStep.edge.toFareyCellPacket.residue
      ∧
    P.prefixCellResidueSum -
        P.failureStep.edge.toFareyCellPacket.G *
          (P.prefixNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt P.boundary
      ∧
    - normalizedSeparationDefectInt P.boundary +
        P.failureStep.edge.toFareyCellPacket.G *
          (P.prefixNoCarryCount : ℤ) ≤
      P.prefixCellResidueSum +
        P.failureStep.edge.toFareyCellPacket.residue := by
  exact
    ⟨P.lower_normalized_neg,
      P.upper_normalized_nonneg,
      P.upper_eq_lower_add_failureResidue,
      P.lower_exact_cell_barrier,
      P.boundarySafety_add_gap_mul_prefixNoCarryCount_le_prefixCellResidueSum_add_failureResidue⟩

/--
A boundary -> B first failure の全-prefix first-passage packet。

`safe_barrier` が「その直前までどれだけ長くても全て negative」という情報を
一つの universal field として保持する。
-/
structure ExactCellFirstPassageBarrierPacket
    (target : ParityWord) where
  provenance : FirstFailureProvenance target

  boundary_le_neg_one :
    normalizedSeparationDefectInt provenance.boundary ≤ -1

  safe_barrier :
    ∀ {mid : ParityWord}
      (C : FerrersChain provenance.boundary mid),
      WordPureSeparation mid →
      normalizedSeparationDefectInt mid =
          normalizedSeparationDefectInt provenance.boundary +
            C.normalizedCellResidueSum -
            (wordTerminalGap provenance.boundary : ℤ) *
              (C.normalizedNoCarryCount : ℤ)
        ∧
      normalizedSeparationDefectInt mid < 0

  lower_neg :
    normalizedSeparationDefectInt provenance.lower < 0

  upper_nonneg :
    0 ≤ normalizedSeparationDefectInt provenance.upper

  final_jump :
    normalizedSeparationDefectInt provenance.upper =
      normalizedSeparationDefectInt provenance.lower +
        provenance.failureStep.edge.toFareyCellPacket.residue

namespace ExactCellFirstPassageBarrierPacket

/-- packet から chain-independent な safe barrier inequality を直接読む。 -/
theorem safe_reachable_barrier
    {target mid : ParityWord}
    (B : ExactCellFirstPassageBarrierPacket target)
    (C : FerrersChain B.provenance.boundary mid)
    (hSafe : WordPureSeparation mid) :
    C.normalizedCellResidueSum -
        (wordTerminalGap B.provenance.boundary : ℤ) *
          (C.normalizedNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt B.provenance.boundary := by
  have h := B.safe_barrier C hSafe
  linarith [h.1, h.2]

end ExactCellFirstPassageBarrierPacket

/-- provenance から全-prefix first-passage packet を canonical に構成する。 -/
def toExactCellFirstPassageBarrierPacket
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    ExactCellFirstPassageBarrierPacket target := by
  refine {
    provenance := P
    boundary_le_neg_one := P.boundary_normalized_le_neg_one
    safe_barrier := ?_
    lower_neg := P.lower_normalized_neg
    upper_nonneg := P.upper_normalized_nonneg
    final_jump := P.upper_eq_lower_add_failureResidue
  }
  intro mid C hSafe
  have h := P.every_safe_reachable_endpoint_exact_cell_barrier C hSafe
  exact ⟨h.1, h.2.1⟩

end FirstFailureProvenance

/-! ## 3. actual A -> B packet bridge -/

namespace ExternalArithmetic

/--
actual obstruction packet は追加仮定なしで全 safe-prefix barrier を持つ。
-/
theorem ActualABObstructionPacket.every_safe_prefix_exact_cell_barrier
    {target mid : ParityWord}
    (A : ActualABObstructionPacket target)
    (C : FerrersChain A.cocycle.provenance.boundary mid)
    (hMidSafe : WordPureSeparation mid) :
    C.normalizedCellResidueSum -
        (wordTerminalGap A.cocycle.provenance.boundary : ℤ) *
          (C.normalizedNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt A.cocycle.provenance.boundary := by
  have h :=
    A.cocycle.provenance.every_safe_reachable_endpoint_exact_cell_barrier
      C hMidSafe
  exact h.2.2

/--
actual packet の final cell は、全 safe-prefix barrier の直後に初めて zero crossing を完成する。
-/
theorem ActualABObstructionPacket.final_exact_cell_first_crossing
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    normalizedSeparationDefectInt A.cocycle.provenance.lower < 0
      ∧
    0 ≤ normalizedSeparationDefectInt A.cocycle.provenance.upper
      ∧
    normalizedSeparationDefectInt A.cocycle.provenance.upper =
      normalizedSeparationDefectInt A.cocycle.provenance.lower +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue
      ∧
    A.cocycle.provenance.prefixCellResidueSum -
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
          (A.cocycle.provenance.prefixNoCarryCount : ℤ) <
      - normalizedSeparationDefectInt A.cocycle.provenance.boundary := by
  have h := A.cocycle.provenance.final_cell_first_crossing
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩


/--
nontrivial bad first-passage target が存在すれば、actual A theorem から
全 safe reachable endpoint barrier と final first crossing を同時に持つ obstruction が得られる。
-/
theorem exists_actualABObstructionPacket_with_safePrefixFirstPassage
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    ∃ A : ActualABObstructionPacket target,
      (∀ {mid : ParityWord}
        (C : FerrersChain A.cocycle.provenance.boundary mid),
        WordPureSeparation mid →
        C.normalizedCellResidueSum -
            (wordTerminalGap A.cocycle.provenance.boundary : ℤ) *
              (C.normalizedNoCarryCount : ℤ) <
          - normalizedSeparationDefectInt A.cocycle.provenance.boundary)
      ∧
      normalizedSeparationDefectInt A.cocycle.provenance.lower < 0
      ∧
      0 ≤ normalizedSeparationDefectInt A.cocycle.provenance.upper
      ∧
      normalizedSeparationDefectInt A.cocycle.provenance.upper =
        normalizedSeparationDefectInt A.cocycle.provenance.lower +
          A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  rcases
      exists_actualABObstructionPacket
        R hTargetFP hTargetFail hTargetNontrivial with
    ⟨A⟩
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro mid C hSafe
    exact A.every_safe_prefix_exact_cell_barrier C hSafe
  · exact A.cocycle.provenance.lower_normalized_neg
  · exact A.cocycle.provenance.upper_normalized_nonneg
  · exact A.cocycle.provenance.upper_eq_lower_add_failureResidue

end ExternalArithmetic

end CSTMicro
end Collatz2
