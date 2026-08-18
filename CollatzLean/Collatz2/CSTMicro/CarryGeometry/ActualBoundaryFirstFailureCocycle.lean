import CollatzLean.Collatz2.CSTMicro.CarryGeometry.NormalizedFerrersLedger
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin

/-!
# Actual A-boundary -> B first-failure cocycle

`ActualBoundaryAFromRhin` は reviewed external input `RhinLinearForm14` だけから
nontrivial Ferrers boundary の `WordPureSeparation` を証明する。

このファイルではその actual A theorem を
`FirstFailureProvenance` と `NormalizedFerrersLedger` に直接接続する。

したがって nontrivial bad first-passage target があれば、

* boundary は target length の explicit critical Sturmian boundary
* boundary normalized defect は at most `-1`
* boundary から first-failure lower までの previous carry residue を符号付きで全て保持
* no-carry move の loss は nonnegative に累積
* final failure carry residue が zero crossing を完成させる

という actual A -> B packet が得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. actual A safety を使った provenance extraction -/

/--
`RhinLinearForm14` による actual Boundary A safety から、
nontrivial bad first-passage target の first-failure provenance を抽出する。

既存 `exists_firstFailureProvenance_from_bad_word` は全 length の boundary safety を
一様に要求するため、ここでは target と同じ length の boundary を先に抽出し、
chain の length preservation から `2 < boundary.length` を得て
actual A theorem を直接適用する。
-/
theorem exists_actual_firstFailureProvenance_from_bad_word
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    Nonempty (FirstFailureProvenance target) := by
  rcases exists_ferrersBoundary_chain hTargetFP with
    ⟨boundary, hBoundary, ⟨C⟩⟩
  have hBoundaryLength : boundary.length = target.length :=
    C.length_eq
  have hBoundaryNontrivial : 2 < boundary.length := by
    rw [hBoundaryLength]
    exact hTargetNontrivial
  have hBoundarySafe : WordPureSeparation boundary :=
    boundaryA_eliminated_from_RhinLinearForm14
      R boundary hBoundary hBoundaryNontrivial
  rcases
      C.safe_or_exists_safePrefix_failure hBoundarySafe with
    hAllSafe | hFailure
  · rcases hAllSafe with ⟨SC⟩
    exact False.elim (hTargetFail SC.finish_safe)
  · rcases hFailure with
      ⟨lower, upper,
        ⟨safePrefixChain⟩,
        ⟨failureStep⟩,
        hUpperFail,
        ⟨failureSuffixChain⟩⟩
    exact
      ⟨{
        boundary := boundary
        lower := lower
        upper := upper
        boundary_isBoundary := hBoundary
        target_firstPassage := hTargetFP
        target_failure := hTargetFail
        safePrefixChain := safePrefixChain
        failureStep := failureStep
        upper_failure := hUpperFail
        failureSuffixChain := failureSuffixChain
      }⟩

/-! ## 2. actual A -> B ledger packet -/

/--
actual A theorem から得られる first-failure cocycle packet。

`provenance` 自体が boundary, safe prefix, distinguished failure edge,
suffix to target を lossless に保持する。
-/
structure ActualBoundaryFirstFailureCocyclePacket
    (target : ParityWord) where
  provenance : FirstFailureProvenance target

  boundary_eq_critical :
    provenance.boundary =
      criticalBoundaryWord target.length

  boundary_normalized_le_neg_one :
    normalizedSeparationDefectInt provenance.boundary ≤ -1

  prefix_noCarryLoss_nonneg :
    0 ≤ provenance.prefixNoCarryLoss

  exact_ledger :
    normalizedSeparationDefectInt provenance.upper =
      normalizedSeparationDefectInt provenance.boundary +
        provenance.prefixCarryContribution -
        provenance.prefixNoCarryLoss +
        provenance.failureStep.edge.toFareyCellPacket.residue

  crossing_budget :
    - normalizedSeparationDefectInt provenance.boundary +
        provenance.prefixNoCarryLoss ≤
      provenance.prefixCarryContribution +
        provenance.failureStep.edge.toFareyCellPacket.residue

  one_le_total_carry :
    1 ≤
      provenance.prefixCarryContribution +
        provenance.failureStep.edge.toFareyCellPacket.residue

  failure_residue_pos :
    0 < provenance.failureStep.edge.toFareyCellPacket.residue

namespace ActualBoundaryFirstFailureCocyclePacket

/-- packet の distinguished B edge を既存 API へ忘却する。 -/
def firstFailureEdge
    {target : ParityWord}
    (A : ActualBoundaryFirstFailureCocyclePacket target) :
    FirstFailureEdge :=
  A.provenance.toFirstFailureEdge

/-- actual packet の distinguished failure edge は carry。 -/
theorem failure_hasCarry
    {target : ParityWord}
    (A : ActualBoundaryFirstFailureCocyclePacket target) :
    A.provenance.failureStep.edge.HasCarry :=
  A.provenance.failure_hasCarry

/-- actual packet の first-failure upper は normalized strip の nonnegative side。 -/
theorem upper_normalized_nonneg
    {target : ParityWord}
    (A : ActualBoundaryFirstFailureCocyclePacket target) :
    0 ≤ normalizedSeparationDefectInt A.provenance.upper :=
  A.provenance.upper_normalized_nonneg

/-- actual packet の first-failure lower は normalized strip の negative side。 -/
theorem lower_normalized_neg
    {target : ParityWord}
    (A : ActualBoundaryFirstFailureCocyclePacket target) :
    normalizedSeparationDefectInt A.provenance.lower < 0 :=
  A.provenance.lower_normalized_neg

end ActualBoundaryFirstFailureCocyclePacket

/-!
## 3. bad word / CST failure から actual packet を構成
-/

/--
nontrivial bad first-passage word は、
reviewed `RhinLinearForm14` だけを外部入力として actual A -> B ledger packet を持つ。
-/
theorem exists_actualBoundaryFirstFailureCocycle
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    Nonempty (ActualBoundaryFirstFailureCocyclePacket target) := by
  rcases
      exists_actual_firstFailureProvenance_from_bad_word
        R hTargetFP hTargetFail hTargetNontrivial with
    ⟨P⟩
  exact
    ⟨{
      provenance := P
      boundary_eq_critical :=
        P.boundary_eq_criticalBoundaryWord_targetLength
      boundary_normalized_le_neg_one :=
        P.boundary_normalized_le_neg_one
      prefix_noCarryLoss_nonneg :=
        P.prefixNoCarryLoss_nonneg
      exact_ledger :=
        P.upper_eq_boundary_add_prefixCarryContribution_sub_noCarryLoss_add_failureResidue
      crossing_budget :=
        P.boundarySafety_add_noCarryLoss_le_prefixCarry_add_failureResidue
      one_le_total_carry :=
        P.one_le_prefixCarryContribution_add_failureResidue
      failure_residue_pos :=
        P.failureResidue_pos
    }⟩

/--
nontrivial `MicroObject` CST failure から actual A -> B ledger packet を抽出する。

A side の唯一の外部入力は `RhinLinearForm14`。
-/
theorem exists_actualBoundaryFirstFailureCocycle_of_cst_failure
    (R : RhinLinearForm14)
    (M : MicroObject)
    (hFail : ¬ M.CSTHolds)
    (hNontrivial : 2 < M.path.word.length) :
    Nonempty
      (ActualBoundaryFirstFailureCocyclePacket M.path.word) := by
  exact
    exists_actualBoundaryFirstFailureCocycle
      R
      M.path.isFirstPassageWord
      (M.wordPureSeparation_failure_of_cst_failure hFail)
      hNontrivial

end ExternalArithmetic
end CSTMicro
end Collatz2
