import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RelativeRankCellCostLedger

/-!
# Weighted-rank global cost bridge

Step 4--5 の local rank-cell insertion と global positive-cost ledger を、
既存 first-failure weighted-rank identity

  weightedRankSum = 3 q     (mod G)

へ接続する。

positive-cost winding equation

  q_B = q_A + G*c - totalCost

を mod `G` に落とすと carry winding 項は消え、

  weightedRankSum(B)
    = 3 * (q_A - totalCost)                    (mod G)

となる。

さらに `relativeRankCellCostSum = 6 * totalCost` と `2*halfUnitValue = 1` から

  weightedRankSum(B)
    = 3*q_A - halfUnitValue*relativeRankCellCostSum

を得る。これは global winding と weighted-rank が同じ cell ledger の二投影であることを
直接表す。
-/

namespace Collatz2
namespace CSTMicro

namespace FirstFailureEdge

/--
normalized winding equation が与えられれば、gap multiple を消して weighted-rank を
`3 * (start - cost)` に落とせる純粋 modular lemma。
-/
theorem weightedRankSum_eq_three_mul_start_sub_cost
    (F : FirstFailureEdge)
    (R : Collatz2.Word.RankUnitData F.upperExponentWord)
    (qStart winding cost : ℤ)
    (hEq :
      (F.upperNormalizedDefectNat : ℤ) =
        qStart +
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) * winding -
          cost) :
    Collatz2.Word.weightedRankSum R =
      (3 : ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) *
        ((qStart - cost : ℤ) :
          ZMod (Collatz2.Word.terminalGap F.upperExponentWord)) := by
  let G := Collatz2.Word.terminalGap F.upperExponentWord
  have hWeighted := F.weightedRankSum_eq_three_mul_upperNormalizedDefectNat R
  have hQCast :
      ((F.upperNormalizedDefectNat : ℕ) : ZMod G) =
        ((qStart - cost : ℤ) : ZMod G) := by
    calc
      ((F.upperNormalizedDefectNat : ℕ) : ZMod G)
          = (((F.upperNormalizedDefectNat : ℤ)) : ZMod G) := by
              simp
      _ =
        ((qStart + (G : ℤ) * winding - cost : ℤ) : ZMod G) := by
          rw [hEq]
      _ = ((qStart - cost : ℤ) : ZMod G) := by
          push_cast
          simp
  calc
    Collatz2.Word.weightedRankSum R
        = (3 : ZMod G) *
            ((F.upperNormalizedDefectNat : ℕ) : ZMod G) := by
              symm
              simpa [G] using hWeighted
    _ = (3 : ZMod G) * ((qStart - cost : ℤ) : ZMod G) := by
          rw [hQCast]

end FirstFailureEdge

namespace ExternalArithmetic
namespace ActualABObstructionPacket

/-- boundary と first-failure upper は同じ terminal gap を持つ。 -/
theorem boundary_wordTerminalGap_eq_upperExponent_terminalGap
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    wordTerminalGap A.cocycle.provenance.boundary =
      Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord := by
  have hChainGap :
      wordTerminalGap A.cocycle.provenance.boundary =
        wordTerminalGap A.cocycle.provenance.upper := by
    unfold wordTerminalGap
    rw [A.boundaryToFailureChain.length_eq]
    rw [A.boundaryToFailureChain.oddCount_eq]
  have hUpper :
      A.firstFailureEdge.step.edge.upperWord =
        A.cocycle.provenance.upper := by
    change
      A.cocycle.provenance.failureStep.edge.upperWord =
        A.cocycle.provenance.upper
    exact A.cocycle.provenance.failureStep.upper_eq.symm
  have hEncoded := A.firstFailureEdge.upperExponentWord_terminalGap
  calc
    wordTerminalGap A.cocycle.provenance.boundary
        = wordTerminalGap A.cocycle.provenance.upper := hChainGap
    _ = wordTerminalGap A.firstFailureEdge.step.edge.upperWord :=
      (congrArg wordTerminalGap hUpper).symm
    _ = Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord :=
      hEncoded.symm

/--
primitive actual packet では weighted-rank は boundary normalized shadow から
`3 * totalCost` を引いたものになる。
-/
theorem exists_weightedRankSum_eq_three_mul_boundary_sub_cost_of_coprime
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hcop :
      Nat.Coprime
        A.firstFailureEdge.step.edge.length
        A.firstFailureEdge.step.edge.oddTotal) :
    ∃ R : Collatz2.Word.RankUnitData A.firstFailureEdge.upperExponentWord,
      Collatz2.Word.weightedRankSum R =
        (3 : ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) *
          ((normalizedSeparationDefectInt A.cocycle.provenance.boundary -
              A.boundaryToFailureCellCost : ℤ) :
            ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) := by
  let F := A.firstFailureEdge
  have hcopWord :
      Nat.Coprime
        (Collatz2.Word.twoSteps F.upperExponentWord)
        (Collatz2.Word.oddSteps F.upperExponentWord) := by
    simpa [F] using hcop
  obtain ⟨R⟩ :=
    F.upperExponentWord_firstCrossing.exists_rankUnitData_of_coprime hcopWord
  have hGap := A.boundary_wordTerminalGap_eq_upperExponent_terminalGap
  have hQ := A.q_cast_eq_boundary_add_gap_mul_winding_sub_cost
  rw [hGap] at hQ
  have hqCanonical : A.q = F.upperNormalizedDefectNat := by
    simpa [F, ActualABObstructionPacket.firstFailureEdge] using A.q_eq_canonical
  have hEq :
      (F.upperNormalizedDefectNat : ℤ) =
        normalizedSeparationDefectInt A.cocycle.provenance.boundary +
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) *
            (A.boundaryToFailureCarryWinding : ℤ) -
          A.boundaryToFailureCellCost := by
    calc
      (F.upperNormalizedDefectNat : ℤ)
          = (A.q : ℤ) := by
              exact_mod_cast hqCanonical.symm
      _ =
        normalizedSeparationDefectInt A.cocycle.provenance.boundary +
          (Collatz2.Word.terminalGap F.upperExponentWord : ℤ) *
            (A.boundaryToFailureCarryWinding : ℤ) -
          A.boundaryToFailureCellCost := hQ
  refine ⟨R, ?_⟩
  simpa [F] using
    F.weightedRankSum_eq_three_mul_start_sub_cost
      R
      (normalizedSeparationDefectInt A.cocycle.provenance.boundary)
      (A.boundaryToFailureCarryWinding : ℤ)
      A.boundaryToFailureCellCost
      hEq

/--
relative rank-cell sum の half-unit image は exact に `3 * totalCost`。
-/
theorem halfUnitValue_mul_relativeRankCellCostSum_cast_eq_three_mul_cellCost
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (R : Collatz2.Word.RankUnitData A.firstFailureEdge.upperExponentWord) :
    Collatz2.Word.halfUnitValue R *
        (A.boundaryToFailureRelativeRankCellSum :
          ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) =
      (3 : ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) *
        (A.boundaryToFailureCellCost :
          ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) := by
  let G := Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord
  have hSum := A.boundaryToFailureRelativeRankCellSum_eq_six_mul_cellCost
  have hCast := congrArg (fun z : ℤ => (z : ZMod G)) hSum
  push_cast at hCast
  have hHalfRaw := R.halfUnitValue_mul_two_eq_one
  have hHalf :
      Collatz2.Word.halfUnitValue R * (2 : ZMod G) = 1 := by
    simpa [G] using hHalfRaw
  calc
    Collatz2.Word.halfUnitValue R *
        (A.boundaryToFailureRelativeRankCellSum : ZMod G)
        =
      Collatz2.Word.halfUnitValue R *
        ((6 : ZMod G) * (A.boundaryToFailureCellCost : ZMod G)) := by
          rw [hCast]
    _ =
      (3 : ZMod G) *
        ((Collatz2.Word.halfUnitValue R * (2 : ZMod G)) *
          (A.boundaryToFailureCellCost : ZMod G)) := by
            ring
    _ = (3 : ZMod G) *
          (A.boundaryToFailureCellCost : ZMod G) := by
            rw [hHalf]
            ring

/--
primitive actual packet の最終形。

weighted-rank(B) は boundary shadow `3*q_A` から、relative rank-cell ledger の
half-unit image を引いたもの。
-/
theorem exists_weightedRankSum_eq_boundaryShadow_sub_half_relativeRankCellSum_of_coprime
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hcop :
      Nat.Coprime
        A.firstFailureEdge.step.edge.length
        A.firstFailureEdge.step.edge.oddTotal) :
    ∃ R : Collatz2.Word.RankUnitData A.firstFailureEdge.upperExponentWord,
      Collatz2.Word.weightedRankSum R =
        (3 : ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) *
            ((normalizedSeparationDefectInt A.cocycle.provenance.boundary : ℤ) :
              ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) -
          Collatz2.Word.halfUnitValue R *
            (A.boundaryToFailureRelativeRankCellSum :
              ZMod (Collatz2.Word.terminalGap A.firstFailureEdge.upperExponentWord)) := by
  obtain ⟨R, hW⟩ :=
    A.exists_weightedRankSum_eq_three_mul_boundary_sub_cost_of_coprime hcop
  have hCell :=
    A.halfUnitValue_mul_relativeRankCellCostSum_cast_eq_three_mul_cellCost R
  refine ⟨R, ?_⟩
  rw [hW, hCell]
  push_cast
  ring

end ActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
