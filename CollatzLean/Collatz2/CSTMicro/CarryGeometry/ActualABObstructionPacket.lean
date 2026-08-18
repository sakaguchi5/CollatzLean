import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CanonicalRepresentativeTrace
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ActualBoundaryFirstFailureCocycle

/-!
# Actual A -> B final obstruction packet

前段までで

* actual A boundary -> first failure の provenance / carry ledger
* B first-failure の bounded Farey strip `0 <= q < D < G`
* canonical least representative の actual Collatz trace
* primitive endpoint における weighted-rank congruence

が別々に得られている。

このファイルではそれらを同じ object に統合する。

一般 packet では非 primitive branch を勝手に消さず、

  A-side ledger
  + bounded B strip
  + actual near-return
  + least representative の cylinder uniqueness

を保持する。

endpoint pair が primitive `gcd(k,m)=1` の場合だけ
`PrimitiveActualABObstructionPacket` へ昇格し、

  weightedRankSum = 3q mod G

を追加する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. actual general A -> B obstruction packet -/

/--
A-side provenance/ledger と B-side bounded strip / actual trace を
一つにまとめた final general packet。
-/
structure ActualABObstructionPacket
    (target : ParityWord) where
  cocycle : ActualBoundaryFirstFailureCocyclePacket target

  q : ℕ
  q_eq_canonical :
    q = cocycle.firstFailureEdge.upperNormalizedDefectNat

  q_lt_m :
    q <
      Collatz2.Word.oddSteps
        cocycle.firstFailureEdge.upperExponentWord

  q_lt_failureResidue :
    (q : ℤ) <
      cocycle.firstFailureEdge.toFirstFailureFareyData.farey.residue

  failureResidue_pos :
    0 <
      cocycle.firstFailureEdge.toFirstFailureFareyData.farey.residue

  failureResidue_lt_gap :
    cocycle.firstFailureEdge.toFirstFailureFareyData.farey.residue <
      cocycle.firstFailureEdge.toFirstFailureFareyData.farey.G

  upper_exact :
    ExactRealizes
      cocycle.firstFailureEdge.step.edge.upperWord
      cocycle.firstFailureEdge.step.edge.upperR
      (cocycle.firstFailureEdge.step.edge.upperR + q)

  cylinder_nondecreasing_iff_zero :
    ∀ n : ℕ,
      cocycle.firstFailureEdge.step.edge.upperR +
            n * cocycle.firstFailureEdge.step.edge.modulus ≤
          representativeAffineEndpoint
              cocycle.firstFailureEdge.step.edge.upperWord +
            n * 3 ^ cocycle.firstFailureEdge.step.edge.oddTotal
        ↔
      n = 0

namespace ActualABObstructionPacket

/-- packet の distinguished B first-failure edge。 -/
def firstFailureEdge
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    FirstFailureEdge :=
  A.cocycle.firstFailureEdge

/-- packet の canonical first-failure Farey data。 -/
def fareyData
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    FirstFailureFareyData A.firstFailureEdge :=
  A.firstFailureEdge.toFirstFailureFareyData

/-- q を integer に戻すと upper normalized defect。 -/
theorem q_cast_eq_upper_normalized
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    (A.q : ℤ) =
      normalizedSeparationDefectInt
        A.firstFailureEdge.step.edge.upperWord := by
  rw [A.q_eq_canonical]
  exact A.firstFailureEdge.upperNormalizedDefectNat_cast

/-- actual B strip の `q < D`。 -/
theorem q_lt_residue
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    (A.q : ℤ) < A.fareyData.farey.residue := by
  simpa [fareyData, firstFailureEdge] using A.q_lt_failureResidue

/-- actual B strip の `0 < D`。 -/
theorem residue_pos
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    0 < A.fareyData.farey.residue := by
  simpa [fareyData, firstFailureEdge] using A.failureResidue_pos

/-- actual B strip の `D < G`。 -/
theorem residue_lt_gap
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.fareyData.farey.residue < A.fareyData.farey.G := by
  simpa [fareyData, firstFailureEdge] using A.failureResidue_lt_gap

/-- actual packet の bounded Farey interval `0 <= q < D < G`。 -/
theorem bounded_strip
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    0 ≤ (A.q : ℤ) ∧
      (A.q : ℤ) < A.fareyData.farey.residue ∧
      0 < A.fareyData.farey.residue ∧
      A.fareyData.farey.residue < A.fareyData.farey.G := by
  exact
    ⟨Int.natCast_nonneg A.q,
      A.q_lt_residue,
      A.residue_pos,
      A.residue_lt_gap⟩

/--
A-side ledger budget を final packet から直接読む。

boundary safety と no-carry loss を、
previous carry contribution と final D が打ち消さなければならない。
-/
theorem crossing_budget
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    - normalizedSeparationDefectInt A.cocycle.provenance.boundary +
        A.cocycle.provenance.prefixNoCarryLoss ≤
      A.cocycle.provenance.prefixCarryContribution +
        A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue :=
  A.cocycle.crossing_budget

/-- A boundary は target length の explicit critical word。 -/
theorem boundary_eq_critical
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.cocycle.provenance.boundary =
      criticalBoundaryWord target.length :=
  A.cocycle.boundary_eq_critical

/-- actual near-return は canonical q で `R -> R+q`。 -/
theorem upper_exactRealizes
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    ExactRealizes
      A.firstFailureEdge.step.edge.upperWord
      A.firstFailureEdge.step.edge.upperR
      (A.firstFailureEdge.step.edge.upperR + A.q) := by
  simpa [firstFailureEdge] using A.upper_exact

/--
upper parity cylinder の nondecreasing start は canonical least representative だけ。
-/
theorem unique_nondecreasing_cylinder_start
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (n : ℕ) :
    A.firstFailureEdge.step.edge.upperR +
          n * A.firstFailureEdge.step.edge.modulus ≤
        representativeAffineEndpoint
            A.firstFailureEdge.step.edge.upperWord +
          n * 3 ^ A.firstFailureEdge.step.edge.oddTotal
      ↔
    n = 0 := by
  simpa [firstFailureEdge] using A.cylinder_nondecreasing_iff_zero n

end ActualABObstructionPacket

/-! ## 2. actual packet の canonical construction -/

/--
既存 actual A -> B cocycle packet を、bounded strip と actual trace を持つ
final obstruction packet へ canonical に昇格する。
-/
def ActualBoundaryFirstFailureCocyclePacket.toActualABObstructionPacket
    {target : ParityWord}
    (C : ActualBoundaryFirstFailureCocyclePacket target) :
    ActualABObstructionPacket target := by
  let F := C.firstFailureEdge
  let D := F.toFirstFailureFareyData
  refine {
    cocycle := C
    q := F.upperNormalizedDefectNat
    q_eq_canonical := rfl
    q_lt_m := F.upperNormalizedDefectNat_lt_oddSteps
    q_lt_failureResidue := ?_
    failureResidue_pos := ?_
    failureResidue_lt_gap := ?_
    upper_exact := F.upperCanonical_exactRealizes
    cylinder_nondecreasing_iff_zero := F.upperCylinder_nondecreasing_iff_index_zero
  }
  · change
      (F.upperNormalizedDefectNat : ℤ) <
        D.farey.residue
    rw [F.upperNormalizedDefectNat_cast]
    exact D.upper_normalizedSeparationDefectInt_lt_residue
  · exact D.residue_pos
  · exact D.residue_lt_gap

/--
nontrivial bad first-passage target は `RhinLinearForm14` から
final actual A -> B obstruction packet を持つ。
-/
theorem exists_actualABObstructionPacket
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    Nonempty (ActualABObstructionPacket target) := by
  rcases
      exists_actualBoundaryFirstFailureCocycle
        R hTargetFP hTargetFail hTargetNontrivial with
    ⟨C⟩
  exact ⟨C.toActualABObstructionPacket⟩

/-- nontrivial `MicroObject` CST failure から final actual packet を抽出。 -/
theorem exists_actualABObstructionPacket_of_cst_failure
    (R : RhinLinearForm14)
    (M : MicroObject)
    (hFail : ¬ M.CSTHolds)
    (hNontrivial : 2 < M.path.word.length) :
    Nonempty (ActualABObstructionPacket M.path.word) := by
  rcases
      exists_actualBoundaryFirstFailureCocycle_of_cst_failure
        R M hFail hNontrivial with
    ⟨C⟩
  exact ⟨C.toActualABObstructionPacket⟩

/-! ## 3. primitive endpoint で weighted-rank を追加 -/

/--
primitive endpoint の final packet。

general packet をそのまま保持し、RankUnitData と
`weightedRankSum = 3q mod G` だけを追加する。
-/
structure PrimitiveActualABObstructionPacket
    (target : ParityWord) where
  base : ActualABObstructionPacket target
  rankUnit :
    Collatz2.Word.RankUnitData
      base.firstFailureEdge.upperExponentWord
  weightedRank :
    (((3 : ℕ) :
        ZMod
          (Collatz2.Word.terminalGap
            base.firstFailureEdge.upperExponentWord))) *
        ((base.q : ℕ) :
          ZMod
            (Collatz2.Word.terminalGap
              base.firstFailureEdge.upperExponentWord)) =
      Collatz2.Word.weightedRankSum rankUnit

namespace ActualABObstructionPacket

/--
endpoint pair `(k,m)` が coprime なら general packet は primitive packet へ昇格する。
-/
theorem exists_primitive_of_coprime
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hcop :
      Nat.Coprime
        A.firstFailureEdge.step.edge.length
        A.firstFailureEdge.step.edge.oddTotal) :
    Nonempty (PrimitiveActualABObstructionPacket target) := by
  let F := A.firstFailureEdge
  have hcopWord :
      Nat.Coprime
        (Collatz2.Word.twoSteps F.upperExponentWord)
        (Collatz2.Word.oddSteps F.upperExponentWord) := by
    simpa [F] using hcop
  obtain ⟨RU⟩ :=
    F.upperExponentWord_firstCrossing.exists_rankUnitData_of_coprime
      hcopWord
  have hWeighted :=
    F.weightedRankSum_eq_three_mul_upperNormalizedDefectNat RU
  have hq : A.q = F.upperNormalizedDefectNat := by
    simpa [F, firstFailureEdge] using A.q_eq_canonical
  refine ⟨{
    base := A
    rankUnit := RU
    weightedRank := ?_
  }⟩
  rw [hq]
  simpa [F, firstFailureEdge] using hWeighted

end ActualABObstructionPacket

namespace PrimitiveActualABObstructionPacket

/-- primitive final packet の weighted-rank small residue summary。 -/
theorem weightedRank_small_residue
    {target : ParityWord}
    (P : PrimitiveActualABObstructionPacket target) :
    P.base.q <
        Collatz2.Word.oddSteps
          P.base.firstFailureEdge.upperExponentWord ∧
      (P.base.q : ℤ) =
        normalizedSeparationDefectInt
          P.base.firstFailureEdge.step.edge.upperWord ∧
      (((3 : ℕ) :
          ZMod
            (Collatz2.Word.terminalGap
              P.base.firstFailureEdge.upperExponentWord))) *
          ((P.base.q : ℕ) :
            ZMod
              (Collatz2.Word.terminalGap
                P.base.firstFailureEdge.upperExponentWord)) =
        Collatz2.Word.weightedRankSum P.rankUnit := by
  exact
    ⟨P.base.q_lt_m,
      P.base.q_cast_eq_upper_normalized,
      P.weightedRank⟩

/--
primitive final packet が同時に保持する中心 obstruction。

A-side crossing budget と B-side bounded strip と weighted-rank residue を
一つの conjunction で公開する。
-/
theorem final_obstruction
    {target : ParityWord}
    (P : PrimitiveActualABObstructionPacket target) :
    - normalizedSeparationDefectInt P.base.cocycle.provenance.boundary +
        P.base.cocycle.provenance.prefixNoCarryLoss ≤
      P.base.cocycle.provenance.prefixCarryContribution +
        P.base.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue
    ∧
    0 ≤ (P.base.q : ℤ)
    ∧
    (P.base.q : ℤ) < P.base.fareyData.farey.residue
    ∧
    0 < P.base.fareyData.farey.residue
    ∧
    P.base.fareyData.farey.residue < P.base.fareyData.farey.G
    ∧
    (((3 : ℕ) :
        ZMod
          (Collatz2.Word.terminalGap
            P.base.firstFailureEdge.upperExponentWord))) *
        ((P.base.q : ℕ) :
          ZMod
            (Collatz2.Word.terminalGap
              P.base.firstFailureEdge.upperExponentWord)) =
      Collatz2.Word.weightedRankSum P.rankUnit := by
  have hStrip := P.base.bounded_strip
  exact
    ⟨P.base.crossing_budget,
      hStrip.1,
      hStrip.2.1,
      hStrip.2.2.1,
      hStrip.2.2.2,
      P.weightedRank⟩

end PrimitiveActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
