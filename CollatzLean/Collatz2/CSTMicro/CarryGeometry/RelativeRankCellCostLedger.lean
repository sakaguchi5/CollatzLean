import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RankCellInsertionCost
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.PositiveCostFerrersPotential

/-!
# Relative rank-cell cost ledger

各 first-passage Ferrers step では前ファイルにより

  6 * cellCost = inserted rank-cell weight       (mod G)

が成り立つ。

ここでは modulus を step ごとに transport して無理に同一視せず、まず ordinary integer 側で
各 rank-cell insertion の canonical lift `6 * cellCost` を chain 全体に足す。

この相対 rank-cell sum は

  relativeRankCellCostSum = 6 * normalizedCellCostSum

であり、既存 positive cost potential により endpoint potential difference へ telescope する。
-/

namespace Collatz2
namespace CSTMicro

/-- positive cost potential を rank-cell scale `6` に持ち上げたもの。 -/
def relativeRankCellCostPotential (v : ParityWord) : ℤ :=
  6 * ferrersCellCostPotential v

namespace FerrersStep

/-- 一 step で relative rank-cell potential は `6 * cellCost` 増える。 -/
theorem relativeRankCellCostPotential_upper_eq_lower_add_six_mul_cellCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    relativeRankCellCostPotential upper =
      relativeRankCellCostPotential lower + 6 * S.edge.fareyCellCost := by
  have h := S.ferrersCellCostPotential_upper_eq_lower_add_cellCost
  unfold relativeRankCellCostPotential
  rw [h]
  ring

end FerrersStep

namespace FerrersChain

/-- chain が追加する rank-cell weights の ordinary integer lift の総和。 -/
noncomputable def relativeRankCellCostSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℤ
  | .refl _ => 0
  | .step C S =>
      C.relativeRankCellCostSum + 6 * S.edge.fareyCellCost

/-- relative rank-cell sum は positive cell-cost sum の exact 6倍。 -/
theorem relativeRankCellCostSum_eq_six_mul_normalizedCellCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.relativeRankCellCostSum = 6 * C.normalizedCellCostSum := by
  induction C with
  | refl =>
      simp [relativeRankCellCostSum, normalizedCellCostSum]
  | @step u v C S ih =>
      change
        C.relativeRankCellCostSum + 6 * S.edge.fareyCellCost =
          6 * (C.normalizedCellCostSum + S.edge.fareyCellCost)
      rw [ih]
      ring

/-- relative rank-cell sum は endpoint potential difference だけで決まる。 -/
theorem relativeRankCellCostSum_eq_potential_sub
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.relativeRankCellCostSum =
      relativeRankCellCostPotential finish -
        relativeRankCellCostPotential start := by
  rw [C.relativeRankCellCostSum_eq_six_mul_normalizedCellCostSum]
  rw [C.normalizedCellCostSum_eq_potential_sub]
  unfold relativeRankCellCostPotential
  ring

/-- 同じ endpoints を結ぶ chain では relative rank-cell sum も path-independent。 -/
theorem relativeRankCellCostSum_chain_independent
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish) :
    C₁.relativeRankCellCostSum = C₂.relativeRankCellCostSum := by
  rw [C₁.relativeRankCellCostSum_eq_potential_sub]
  rw [C₂.relativeRankCellCostSum_eq_potential_sub]

end FerrersChain

namespace ExternalArithmetic
namespace ActualABObstructionPacket

/-- actual boundary から distinguished first-failure upper までの underlying Ferrers chain。 -/
def boundaryToFailureChain
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    FerrersChain A.cocycle.provenance.boundary A.cocycle.provenance.upper :=
  FerrersChain.step
    A.cocycle.provenance.safePrefixChain.toFerrersChain
    A.cocycle.provenance.failureStep

/-- actual boundary -> first failure の positive cell cost。 -/
noncomputable def boundaryToFailureCellCost
    {target : ParityWord}
    (A : ActualABObstructionPacket target) : ℤ :=
  A.boundaryToFailureChain.normalizedCellCostSum

/-- actual boundary -> first failure の carry winding。 -/
noncomputable def boundaryToFailureCarryWinding
    {target : ParityWord}
    (A : ActualABObstructionPacket target) : ℕ :=
  A.boundaryToFailureChain.normalizedCarryCount

/-- actual boundary -> first failure の relative rank-cell sum。 -/
noncomputable def boundaryToFailureRelativeRankCellSum
    {target : ParityWord}
    (A : ActualABObstructionPacket target) : ℤ :=
  A.boundaryToFailureChain.relativeRankCellCostSum

/-- actual q を provenance upper の normalized coordinate と直接同定。 -/
theorem q_cast_eq_provenance_upper_normalized
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    (A.q : ℤ) =
      normalizedSeparationDefectInt A.cocycle.provenance.upper := by
  have h := A.q_cast_eq_upper_normalized
  have hUpper :
      A.firstFailureEdge.step.edge.upperWord =
        A.cocycle.provenance.upper := by
    change
      A.cocycle.provenance.failureStep.edge.upperWord =
        A.cocycle.provenance.upper
    exact A.cocycle.provenance.failureStep.upper_eq.symm
  calc
    (A.q : ℤ)
        = normalizedSeparationDefectInt
            A.firstFailureEdge.step.edge.upperWord := h
    _ = normalizedSeparationDefectInt A.cocycle.provenance.upper :=
      congrArg normalizedSeparationDefectInt hUpper

/--
actual A -> B first failure の positive-cost winding equation。
-/
theorem q_cast_eq_boundary_add_gap_mul_winding_sub_cost
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    (A.q : ℤ) =
      normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        (wordTerminalGap A.cocycle.provenance.boundary : ℤ) *
          (A.boundaryToFailureCarryWinding : ℤ) -
        A.boundaryToFailureCellCost := by
  have h :=
    A.boundaryToFailureChain.normalized_finish_eq_start_add_gap_mul_carryCount_sub_cellCostSum
      A.cocycle.provenance.boundary_isBoundary.1
  calc
    (A.q : ℤ)
        = normalizedSeparationDefectInt A.cocycle.provenance.upper :=
          A.q_cast_eq_provenance_upper_normalized
    _ =
      normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        (wordTerminalGap A.cocycle.provenance.boundary : ℤ) *
          (A.boundaryToFailureChain.normalizedCarryCount : ℤ) -
        A.boundaryToFailureChain.normalizedCellCostSum := h
    _ =
      normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        (wordTerminalGap A.cocycle.provenance.boundary : ℤ) *
          (A.boundaryToFailureCarryWinding : ℤ) -
        A.boundaryToFailureCellCost := by
          rfl

/-- actual relative rank-cell sum は total positive cell cost の exact 6倍。 -/
theorem boundaryToFailureRelativeRankCellSum_eq_six_mul_cellCost
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.boundaryToFailureRelativeRankCellSum =
      6 * A.boundaryToFailureCellCost := by
  unfold boundaryToFailureRelativeRankCellSum boundaryToFailureCellCost
  exact A.boundaryToFailureChain.relativeRankCellCostSum_eq_six_mul_normalizedCellCostSum

/-- actual relative rank-cell sum は endpoint potential difference に telescope する。 -/
theorem boundaryToFailureRelativeRankCellSum_eq_potential_sub
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.boundaryToFailureRelativeRankCellSum =
      relativeRankCellCostPotential A.cocycle.provenance.upper -
        relativeRankCellCostPotential A.cocycle.provenance.boundary := by
  unfold boundaryToFailureRelativeRankCellSum
  exact A.boundaryToFailureChain.relativeRankCellCostSum_eq_potential_sub

end ActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
