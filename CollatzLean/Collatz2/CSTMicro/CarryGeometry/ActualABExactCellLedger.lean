import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExactNormalizedFerrersLedger
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ActualABObstructionPacket

set_option linter.style.longLine false

/-!
# Actual A -> B obstruction: exact lifted cell ledger

`ActualABObstructionPacket` に exact cell ledger を追加する薄い最終 bridge。

nontrivial bad first-passage target が存在すれば、reviewed `RhinLinearForm14`
から得られる actual A -> B packet は、従来の

* bounded strip `0 <= q < D < G`,
* actual near-return `R -> R+q`,
* cylinder uniqueness,

に加えて

  q_upper
    = q_boundary
      + prefixCellResidueSum
      + D_failure
      - G * prefixNoCarryCount

という exact lifted Farey ledger を同時に満たす。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace ActualABObstructionPacket

/-- final actual packet から exact lifted cell identity を直接読む。 -/
theorem exact_cell_ledger
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    normalizedSeparationDefectInt A.cocycle.provenance.upper =
      normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        A.cocycle.provenance.prefixCellResidueSum +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue -
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
          (A.cocycle.provenance.prefixNoCarryCount : ℤ) :=
  A.cocycle.provenance.upper_eq_boundary_add_prefixCellResidueSum_add_failureResidue_sub_gap_mul_prefixNoCarryCount

/-- final actual packet の exact cell crossing budget。 -/
theorem exact_cell_crossing_budget
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    - normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
          (A.cocycle.provenance.prefixNoCarryCount : ℤ) ≤
      A.cocycle.provenance.prefixCellResidueSum +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue :=
  A.cocycle.provenance.boundarySafety_add_gap_mul_prefixNoCarryCount_le_prefixCellResidueSum_add_failureResidue

/--
actual final obstruction の strengthened packet。

A-side exact cell ledger、B-side bounded strip、actual near-return を
同じ conjunction で公開する。
-/
theorem exact_cell_final_obstruction
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    normalizedSeparationDefectInt A.cocycle.provenance.upper =
      normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        A.cocycle.provenance.prefixCellResidueSum +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue -
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
          (A.cocycle.provenance.prefixNoCarryCount : ℤ)
    ∧
    - normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
          (A.cocycle.provenance.prefixNoCarryCount : ℤ) ≤
      A.cocycle.provenance.prefixCellResidueSum +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue
    ∧
    0 ≤ (A.q : ℤ)
    ∧
    (A.q : ℤ) < A.fareyData.farey.residue
    ∧
    0 < A.fareyData.farey.residue
    ∧
    A.fareyData.farey.residue < A.fareyData.farey.G
    ∧
    ExactRealizes
      A.firstFailureEdge.step.edge.upperWord
      A.firstFailureEdge.step.edge.upperR
      (A.firstFailureEdge.step.edge.upperR + A.q) := by
  have hStrip := A.bounded_strip
  exact
    ⟨A.exact_cell_ledger,
      A.exact_cell_crossing_budget,
      hStrip.1,
      hStrip.2.1,
      hStrip.2.2.1,
      hStrip.2.2.2,
      A.upper_exactRealizes⟩

end ActualABObstructionPacket

/-!
## Canonical construction
-/

/--
nontrivial bad first-passage target から exact-cell strengthened actual packet が存在する。

object 自体は既存 `ActualABObstructionPacket` のままにし、
新しい exact ledger theorem を追加仮定なしで利用できることを existence で公開する。
-/
theorem exists_actualABObstructionPacket_with_exactCellLedger
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    ∃ A : ActualABObstructionPacket target,
      normalizedSeparationDefectInt A.cocycle.provenance.upper =
        normalizedSeparationDefectInt A.cocycle.provenance.boundary +
          A.cocycle.provenance.prefixCellResidueSum +
          A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue -
          A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
            (A.cocycle.provenance.prefixNoCarryCount : ℤ) ∧
      - normalizedSeparationDefectInt A.cocycle.provenance.boundary +
          A.cocycle.provenance.failureStep.edge.toFareyCellPacket.G *
            (A.cocycle.provenance.prefixNoCarryCount : ℤ) ≤
        A.cocycle.provenance.prefixCellResidueSum +
          A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  rcases
      exists_actualABObstructionPacket
        R hTargetFP hTargetFail hTargetNontrivial with
    ⟨A⟩
  exact ⟨A, A.exact_cell_ledger, A.exact_cell_crossing_budget⟩

end ExternalArithmetic
end CSTMicro
end Collatz2
