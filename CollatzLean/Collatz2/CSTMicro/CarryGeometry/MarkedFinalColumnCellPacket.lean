import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnProfileResidualLedger
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ActualABObstructionPacket

/-!
# Actual B as a marked final column/layer cell

`ColumnProfileResidualLedger` により、critical boundary から first-failure upper `B` までの
rank-top sum は final extra-depth profile `h` だけから `K(h)` として復元できる。
一方 actual first-failure upper には既存 `RankTopWinding` から

  Top(B) = 3*q_B + G*n_B,
  1 <= n_B < m

がある。従って

  G*n_B + 3*q_B = K(h)

を exact に得る。

さらに distinguished failure step は、その marked rank column `k*` の
final top layer `j*` を一個追加する step である。よって

  h(k*) = j* + 1,
  D* = columnLayerFareyResidue(H,m,k*,j*),
  0 <= q_B < D* < G

までを一 packet にまとめる。

これにより actual A -> B obstruction は、chain order ではなく

  final column profile h
  + marked final cell (k*,j*)
  + bounded integers (n_B,q_B)

で記述できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open FerrersStep

namespace ActualABObstructionPacket

/-- actual packet の critical-boundary base rank-top sum。 -/
noncomputable def columnProfileBoundaryTop
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length) : ℤ :=
  let P := A.cocycle.provenance
  let hTargetLen : 1 < target.length := by omega
  let hBoundaryFP : IsFirstPassageWord (criticalBoundaryWord target.length) :=
    criticalBoundaryWord_isFirstPassage P.target_firstPassage
  let hBoundaryLen : 1 < (criticalBoundaryWord target.length).length := by
    simpa using hTargetLen
  (parityRankTopSum
      (criticalBoundaryWord target.length)
      hBoundaryFP hBoundaryLen : ℤ)

/-- actual B の final extra-depth profile から作る `K(h)`。 -/
noncomputable def columnProfileKValue
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length) : ℤ :=
  let P := A.cocycle.provenance
  columnProfileK
    P.upper.length
    (oddCount P.upper)
    (A.columnProfileBoundaryTop hNontrivial)
    (parityExtraDepth P.upper)

/--
actual provenance chain を explicit critical boundary 起点へ transport する。
-/
def criticalBoundaryToUpperChain
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    FerrersChain
      (criticalBoundaryWord target.length)
      A.cocycle.provenance.upper := by
  let P := A.cocycle.provenance
  rw [← P.boundary_eq_criticalBoundaryWord_targetLength]
  exact P.boundaryToUpperRankTopChain

/--
actual safe-prefix chain を explicit critical boundary 起点へ transport する。
-/
def criticalBoundaryToFailureLowerChain
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    FerrersChain
      (criticalBoundaryWord target.length)
      A.cocycle.provenance.lower := by
  let P := A.cocycle.provenance
  rw [← P.boundary_eq_criticalBoundaryWord_targetLength]
  exact P.safePrefixChain.toFerrersChain

/--
actual first-failure rank winding と final profile ledger を結合する。

  G*nB + 3*qB = K(h).
-/
theorem exists_columnProfile_rankTop_equation
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length) :
    ∃ nB : ℕ,
      1 ≤ nB ∧
      nB < Collatz2.Word.oddSteps A.firstFailureEdge.upperExponentWord ∧
      (columnLayerGap
          A.cocycle.provenance.upper.length
          (oddCount A.cocycle.provenance.upper) : ℤ) * (nB : ℤ) +
          3 * (A.q : ℤ) =
        A.columnProfileKValue hNontrivial := by
  let P := A.cocycle.provenance
  let F := A.firstFailureEdge
  let C := A.criticalBoundaryToUpperChain
  have hTargetLen : 1 < target.length := by omega
  have hUpperLen : 1 < P.upper.length := by
    have hEq := P.failureSuffixChain.length_eq
    rw [hEq]
    omega
  have hUpperNontrivial : 2 < P.upper.length := by
    have hEq := P.failureSuffixChain.length_eq
    rw [hEq]
    exact hNontrivial
  have hKRaw :=
    C.parityRankTopSum_eq_columnProfileK
      P.target_firstPassage hTargetLen
  have hK :
      (parityRankTopSum P.upper P.upper_firstPassage hUpperLen : ℤ) =
        A.columnProfileKValue hNontrivial := by
    simpa [
      columnProfileKValue,
      columnProfileBoundaryTop,
      P
    ] using hKRaw
  have hEdgeUpper : F.step.edge.upperWord = P.upper := by
    change P.failureStep.edge.upperWord = P.upper
    exact P.failureStep.upper_eq.symm
  have hFLen : 2 < F.step.edge.upperWord.length := by
    rw [hEdgeUpper]
    exact hUpperNontrivial
  obtain ⟨nB, hnPos, hnLt, hWind⟩ :=
    F.exists_rankTopWinding hFLen
  have hExp :
      F.upperExponentWord = exponentWordOfParity P.upper := by
    change
      exponentWordOfParity F.step.edge.upperWord =
        exponentWordOfParity P.upper
    exact congrArg exponentWordOfParity hEdgeUpper
  have hTopEq :
      Collatz2.Word.rankTopSum F.upperExponentWord_firstCrossing =
        parityRankTopSum P.upper P.upper_firstPassage hUpperLen := by
    unfold parityRankTopSum
    exact
      rankTopSum_eq_of_word_eq
        hExp
        F.upperExponentWord_firstCrossing
        (P.upper_firstPassage.exponentWordOfParity_firstCrossing hUpperLen)
  have hGap :
      Collatz2.Word.terminalGap F.upperExponentWord =
        columnLayerGap P.upper.length (oddCount P.upper) := by
    rw [hExp]
    rw [P.upper_firstPassage.exponentWordOfParity_terminalGap_eq_wordTerminalGap
      hUpperLen]
    rfl
  have hq : A.q = F.upperNormalizedDefectNat := by
    simpa [F, firstFailureEdge] using A.q_eq_canonical
  have hWindZ := congrArg (fun n : ℕ => (n : ℤ)) hWind
  push_cast at hWindZ
  rw [hTopEq, ← hq, hGap, hK] at hWindZ
  refine ⟨nB, hnPos, ?_, ?_⟩
  · simpa [F] using hnLt
  · linarith

end ActualABObstructionPacket

/--
actual B を final profile + marked final cell + bounded `(nB,qB)` へ圧縮した packet。
-/
structure MarkedFinalColumnCellPacket
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length) where
  nB : ℕ
  nB_pos : 1 ≤ nB
  nB_lt_m :
    nB < Collatz2.Word.oddSteps A.firstFailureEdge.upperExponentWord

  rankTop_profile_equation :
    (columnLayerGap
        A.cocycle.provenance.upper.length
        (oddCount A.cocycle.provenance.upper) : ℤ) * (nB : ℤ) +
        3 * (A.q : ℤ) =
      A.columnProfileKValue hNontrivial

  markedColumn : ℕ
  markedLayer : ℕ

  markedColumn_eq_failureRankCut :
    markedColumn =
      A.cocycle.provenance.failureStep.edge.rankCut

  markedLayer_succ_eq_finalDepth :
    parityExtraDepth A.cocycle.provenance.upper markedColumn =
      markedLayer + 1

  failureResidue_eq_markedCell :
    A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue =
      columnLayerFareyResidue
        A.cocycle.provenance.upper.length
        (oddCount A.cocycle.provenance.upper)
        markedColumn markedLayer

  q_nonneg : 0 ≤ (A.q : ℤ)

  q_lt_markedResidue :
    (A.q : ℤ) <
      columnLayerFareyResidue
        A.cocycle.provenance.upper.length
        (oddCount A.cocycle.provenance.upper)
        markedColumn markedLayer

  markedResidue_lt_gap :
    columnLayerFareyResidue
        A.cocycle.provenance.upper.length
        (oddCount A.cocycle.provenance.upper)
        markedColumn markedLayer <
      (columnLayerGap
        A.cocycle.provenance.upper.length
        (oddCount A.cocycle.provenance.upper) : ℤ)

namespace ActualABObstructionPacket

/-- actual obstruction packet から marked final column packet を canonical に構成。 -/
noncomputable def toMarkedFinalColumnCellPacket
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length) :
    MarkedFinalColumnCellPacket A hNontrivial := by
  let P := A.cocycle.provenance
  let S := P.failureStep
  let C := A.criticalBoundaryToFailureLowerChain
  have hTargetLen : 1 < target.length := by omega
  have hkBoundary := C.next_rankCut_lt_criticalBoundary_oddSteps S
  have hLowerDepth :=
    C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
      P.target_firstPassage hTargetLen S hkBoundary
  have hStepDepth :=
    S.parityExtraDepth_selected_step P.lower_firstPassage
  rw [hLowerDepth] at hStepDepth
  have hResidue :=
    C.criticalBoundary_next_fareyResidue_eq_columnLayer
      P.target_firstPassage hTargetLen S hkBoundary
  have hH : S.edge.length = P.upper.length := by
    exact S.edge_length_eq_lower_length.trans S.length_eq
  have hm : S.edge.oddTotal = oddCount P.upper := by
    exact S.edge_oddTotal_eq_lower_oddCount.trans S.oddCount_eq
  rw [hH, hm] at hResidue
  have hGap := S.fareyGap_eq_columnLayerGap_cast P.lower_firstPassage
  rw [hH, hm] at hGap
  have hqD := A.q_lt_residue
  change
    (A.q : ℤ) < S.edge.toFareyCellPacket.residue at hqD
  have hDG := A.residue_lt_gap
  change
    S.edge.toFareyCellPacket.residue <
      S.edge.toFareyCellPacket.G at hDG
  rw [hResidue] at hqD
  rw [hResidue, hGap] at hDG
  have hExists :=
    A.exists_columnProfile_rankTop_equation hNontrivial
  let nB : ℕ := Classical.choose hExists
  have hnSpec := Classical.choose_spec hExists
  have hnPos := hnSpec.1
  have hnLt := hnSpec.2.1
  have hEq := hnSpec.2.2
  refine {
    nB := nB
    nB_pos := hnPos
    nB_lt_m := hnLt
    rankTop_profile_equation := hEq
    markedColumn := S.edge.rankCut
    markedLayer := C.rankColumnOccupancy S.edge.rankCut
    markedColumn_eq_failureRankCut := rfl
    markedLayer_succ_eq_finalDepth := ?_
    failureResidue_eq_markedCell := ?_
    q_nonneg := Int.natCast_nonneg A.q
    q_lt_markedResidue := ?_
    markedResidue_lt_gap := ?_
  }
  · exact hStepDepth
  · exact hResidue
  · exact hqD
  · exact hDG

end ActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
