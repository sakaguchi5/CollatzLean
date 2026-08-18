import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadPredecessorGeometry

/-!
# Minimal bad cell-cost obstruction

minimal bad predecessor geometry では、B に入る任意の first-passage predecessor cell で

  0 < D < G,
  q_B < D,
  R_B < deltaR

が得られた。

このファイルでは Farey residue `D` の complement

  cellCost = G - D

を導入する。

canonical adjacent cell の exact Farey identity

  2^d D = G h - 3^r,
  h = 2^d - u

から

  2^d cellCost = G u + 3^r

を得る。さらに full scale へ戻すと

  2^k cellCost = G deltaR + deltaB.

first-failure edge ではこれを upper defect equation と結合し、

  2^k G - B_upper - deltaB
    = 2^k (D-q_upper) + G (deltaR-R_upper)

という exact scalar margin を得る。

minimal bad predecessor では右辺の二項がとも strict positive なので、
`q<D` と `R<deltaR` を一つの positive obstruction にまとめられる。
-/

namespace Collatz2
namespace CSTMicro

namespace AdjacentFerrersSwap

/-- Farey residue の terminal-gap complement。 -/
def fareyCellCost (S : AdjacentFerrersSwap) : ℤ :=
  S.toFareyCellPacket.G - S.toFareyCellPacket.residue

/-- `D < G` なら cell cost は正。 -/
theorem fareyCellCost_pos_of_residue_lt_gap
    (S : AdjacentFerrersSwap)
    (h : S.toFareyCellPacket.residue < S.toFareyCellPacket.G) :
    0 < S.fareyCellCost := by
  unfold fareyCellCost
  linarith

/-- `0 < D` なら cell cost は gap より小さい。 -/
theorem fareyCellCost_lt_gap_of_residue_pos
    (S : AdjacentFerrersSwap)
    (h : 0 < S.toFareyCellPacket.residue) :
    S.fareyCellCost < S.toFareyCellPacket.G := by
  unfold fareyCellCost
  linarith

/--
canonical adjacent cell の residue complement の exact local identity。

  2^d (G-D) = G*u + 3^r.
-/
theorem twoPow_mul_fareyCellCost_eq_gap_mul_fareyLocalInverse_add_threePow
    (S : AdjacentFerrersSwap) :
    (2 : ℤ) ^ S.fareyTailDepth * S.fareyCellCost =
      S.toFareyCellPacket.G * (S.fareyLocalInverse : ℤ) +
        (3 : ℤ) ^ S.fareyRightExponent := by
  have hResid := S.toFareyCellPacket.twoPow_mul_residue
  have hResid' :
      (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.residue =
        S.toFareyCellPacket.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent := by
    simpa [AdjacentFerrersSwap.toFareyCellPacket] using hResid
  have hH := S.fareyH_cast
  unfold fareyCellCost
  calc
    (2 : ℤ) ^ S.fareyTailDepth *
          (S.toFareyCellPacket.G - S.toFareyCellPacket.residue)
        =
      (2 : ℤ) ^ S.fareyTailDepth * S.toFareyCellPacket.G -
        (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.residue := by ring
    _ =
      (2 : ℤ) ^ S.fareyTailDepth * S.toFareyCellPacket.G -
        (S.toFareyCellPacket.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent) := by
            rw [hResid']
    _ =
      S.toFareyCellPacket.G * (S.fareyLocalInverse : ℤ) +
        (3 : ℤ) ^ S.fareyRightExponent := by
          rw [hH]
          ring

/--
local identity を full scale へ持ち上げる。

  2^k (G-D) = G*deltaR + deltaB.
-/
theorem twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
    (S : AdjacentFerrersSwap) :
    (2 : ℤ) ^ S.length * S.fareyCellCost =
      S.toFareyCellPacket.G * (S.deltaR : ℤ) +
        (S.deltaB : ℤ) := by
  have hCost :=
    S.twoPow_mul_fareyCellCost_eq_gap_mul_fareyLocalInverse_add_threePow
  have hDeltaNat := S.deltaR_eq_twoPow_mul_fareyLocalInverse
  have hDelta :
      (S.deltaR : ℤ) =
        (2 : ℤ) ^ S.position * (S.fareyLocalInverse : ℤ) := by
    exact_mod_cast hDeltaNat
  calc
    (2 : ℤ) ^ S.length * S.fareyCellCost
        =
      (2 : ℤ) ^ S.position *
        ((2 : ℤ) ^ S.fareyTailDepth * S.fareyCellCost) := by
          rw [S.length_eq_position_add_fareyTailDepth, pow_add]
          ring
    _ =
      (2 : ℤ) ^ S.position *
        (S.toFareyCellPacket.G * (S.fareyLocalInverse : ℤ) +
          (3 : ℤ) ^ S.fareyRightExponent) := by
            rw [hCost]
    _ =
      S.toFareyCellPacket.G * (S.deltaR : ℤ) +
        (S.deltaB : ℤ) := by
          rw [hDelta]
          unfold AdjacentFerrersSwap.deltaB
          unfold AdjacentFerrersSwap.fareyRightExponent
          push_cast
          ring_nf

/--
coefficient-contracting な canonical adjacent cell では、carry/no-carry に関係なく
Farey residue は terminal gap より strict に小さい。
-/
theorem fareyResidue_lt_gap_of_contracting
    (S : AdjacentFerrersSwap)
    (hContract : 3 ^ S.oddTotal < S.modulus) :
    S.toFareyCellPacket.residue < S.toFareyCellPacket.G := by
  have hContractNat :
      3 ^ S.oddTotal < 2 ^ S.length := by
    simpa [AdjacentFerrersSwap.modulus] using hContract
  have hContractInt :
      (3 : ℤ) ^ S.oddTotal < (2 : ℤ) ^ S.length := by
    exact_mod_cast hContractNat
  have hG : 0 < S.toFareyCellPacket.G := by
    change
      0 < (2 : ℤ) ^ S.length - (3 : ℤ) ^ S.oddTotal
    linarith
  have hHLtNat := S.fareyH_lt_twoPow
  have hHLt :
      (S.fareyH : ℤ) < (2 : ℤ) ^ S.fareyTailDepth := by
    exact_mod_cast hHLtNat
  have hEq := S.toFareyCellPacket.twoPow_mul_residue
  have hEq' :
      (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.residue =
        S.toFareyCellPacket.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent := by
    simpa [AdjacentFerrersSwap.toFareyCellPacket] using hEq
  have hThree : 0 < (3 : ℤ) ^ S.fareyRightExponent := by
    positivity
  have hSub :
      S.toFareyCellPacket.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent <
        S.toFareyCellPacket.G * (S.fareyH : ℤ) := by
    linarith
  have hMul :
      S.toFareyCellPacket.G * (S.fareyH : ℤ) <
        S.toFareyCellPacket.G *
          (2 : ℤ) ^ S.fareyTailDepth :=
    (Int.mul_lt_mul_left hG).2 hHLt
  have hScaled :
      (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.residue <
        (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.G := by
    calc
      (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.residue
          =
        S.toFareyCellPacket.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent := hEq'
      _ < S.toFareyCellPacket.G * (S.fareyH : ℤ) := hSub
      _ < S.toFareyCellPacket.G *
          (2 : ℤ) ^ S.fareyTailDepth := hMul
      _ = (2 : ℤ) ^ S.fareyTailDepth *
          S.toFareyCellPacket.G := by ring
  have hTwo : 0 < (2 : ℤ) ^ S.fareyTailDepth := by
    positivity
  exact (Int.mul_lt_mul_left hTwo).mp hScaled

/-- contracting canonical cell の cost は strict positive。 -/
theorem fareyCellCost_pos_of_contracting
    (S : AdjacentFerrersSwap)
    (hContract : 3 ^ S.oddTotal < S.modulus) :
    0 < S.fareyCellCost := by
  exact
    S.fareyCellCost_pos_of_residue_lt_gap
      (S.fareyResidue_lt_gap_of_contracting hContract)

end AdjacentFerrersSwap

/-! ## first-failure scalar margin -/

namespace FirstFailureEdge

/--
first-failure の `q<D` と `R<deltaR` を一つに統合する exact identity。

  M*G - B - deltaB
    = M*(D-q) + G*(deltaR-R).
-/
theorem scalarMargin_eq_modulus_mul_residueGap_add_gap_mul_representativeGap
    (F : FirstFailureEdge) :
    let D := F.toFirstFailureFareyData
    (F.step.edge.modulus : ℤ) * D.farey.G -
        (affineConst F.step.edge.upperWord : ℤ) -
        (F.step.edge.deltaB : ℤ) =
      (F.step.edge.modulus : ℤ) *
          (D.farey.residue -
            normalizedSeparationDefectInt F.step.edge.upperWord) +
        D.farey.G *
          ((F.step.edge.deltaR : ℤ) - (F.step.edge.upperR : ℤ)) := by
  let D := F.toFirstFailureFareyData
  have hCostRaw :=
    F.step.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
  have hCost :
      (F.step.edge.modulus : ℤ) *
          (D.farey.G - D.farey.residue) =
        D.farey.G * (F.step.edge.deltaR : ℤ) +
          (F.step.edge.deltaB : ℤ) := by
    change
      (F.step.edge.modulus : ℤ) *
          (F.step.edge.toFareyCellPacket.G -
            F.step.edge.toFareyCellPacket.residue) =
        F.step.edge.toFareyCellPacket.G *
            (F.step.edge.deltaR : ℤ) +
          (F.step.edge.deltaB : ℤ)
    simpa [
      AdjacentFerrersSwap.modulus,
      AdjacentFerrersSwap.fareyCellCost
    ] using hCostRaw
  have hB :=
    F.upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized
  have hG :=
    D.farey_G_eq_wordTerminalGap
  have hGapUL :
      wordTerminalGap F.step.edge.upperWord =
        wordTerminalGap F.step.edge.lowerWord := by
    unfold wordTerminalGap
    rw [
      F.step.edge.upperWord_length,
      F.step.edge.lowerWord_length,
      F.step.edge.upperWord_oddCount,
      F.step.edge.lowerWord_oddCount
    ]
  have hGap :
      (wordTerminalGap F.step.edge.upperWord : ℤ) =
        D.farey.G := by
    calc
      (wordTerminalGap F.step.edge.upperWord : ℤ)
          =
        (wordTerminalGap F.step.edge.lowerWord : ℤ) := by
            exact_mod_cast hGapUL
      _ = D.farey.G := hG.symm
  have hB' :
      (affineConst F.step.edge.upperWord : ℤ) =
        D.farey.G * (F.step.edge.upperR : ℤ) +
          (F.step.edge.modulus : ℤ) *
            normalizedSeparationDefectInt F.step.edge.upperWord := by
    rw [hGap] at hB
    exact hB
  dsimp
  nlinarith [hCost, hB']

/--
first-failure scalar margin は少なくとも `modulus + G`。
両 positive gaps が integer なので各々 1 以上であることを使う。
-/
theorem modulus_add_gap_le_scalarMargin
    (F : FirstFailureEdge) :
    let D := F.toFirstFailureFareyData
    (F.step.edge.modulus : ℤ) + D.farey.G ≤
      (F.step.edge.modulus : ℤ) * D.farey.G -
        (affineConst F.step.edge.upperWord : ℤ) -
        (F.step.edge.deltaB : ℤ) := by
  let D := F.toFirstFailureFareyData
  have hId := F.scalarMargin_eq_modulus_mul_residueGap_add_gap_mul_representativeGap
  dsimp at hId ⊢
  have hQ := D.upper_normalizedSeparationDefectInt_lt_residue
  have hDQ :
      1 ≤ D.farey.residue -
        normalizedSeparationDefectInt F.step.edge.upperWord := by
    omega
  have hCarry := F.hasCarry
  have hRlt := F.step.edge.upperR_lt_deltaR_of_hasCarry hCarry
  have hRltInt :
      (F.step.edge.upperR : ℤ) <
        (F.step.edge.deltaR : ℤ) := by
    exact_mod_cast hRlt
  have hDR :
      1 ≤ (F.step.edge.deltaR : ℤ) -
        (F.step.edge.upperR : ℤ) := by
    omega
  have hM : 0 < (F.step.edge.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  have hG : 0 < D.farey.G := D.gap_pos
  have hTermM :
      (F.step.edge.modulus : ℤ) ≤
        (F.step.edge.modulus : ℤ) *
          (D.farey.residue -
            normalizedSeparationDefectInt F.step.edge.upperWord) := by
    nlinarith
  have hTermG :
      D.farey.G ≤
        D.farey.G *
          ((F.step.edge.deltaR : ℤ) - (F.step.edge.upperR : ℤ)) := by
    nlinarith
  rw [hId]
  linarith

end FirstFailureEdge

/-! ## minimal selected cell の forbidden arc -/

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket
namespace BoundaryRespectingPredecessorCell

/-- selected cell の positive cost。 -/
def cellCost
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) : ℤ :=
  C.step.edge.fareyCellCost

/-- selected minimal-bad cell の cost は正。 -/
theorem cellCost_pos
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    0 < C.cellCost := by
  exact
    C.step.edge.fareyCellCost_pos_of_residue_lt_gap
      C.residue_lt_gap

/-- selected cell の cost は gap より strict に小さい。 -/
theorem cellCost_lt_gap
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.cellCost < C.step.edge.toFareyCellPacket.G := by
  exact
    C.step.edge.fareyCellCost_lt_gap_of_residue_pos
      C.residue_pos

/--
minimality の `q_B < D` を cost 側へ反転する。

  q_B + cellCost < G.
-/
theorem actualQ_add_cellCost_lt_gap
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    (M.actual.q : ℤ) + C.cellCost <
      C.step.edge.toFareyCellPacket.G := by
  unfold cellCost AdjacentFerrersSwap.fareyCellCost
  linarith [C.q_lt_residue]

/-- 同じ条件を `cellCost < G-q_B` として読む。 -/
theorem cellCost_lt_gap_sub_actualQ
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.cellCost <
      C.step.edge.toFareyCellPacket.G - (M.actual.q : ℤ) := by
  linarith [C.actualQ_add_cellCost_lt_gap]

/-- integer strictness を使った forbidden-arc clearance。 -/
theorem one_le_gap_sub_actualQ_sub_cellCost
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    1 ≤ C.step.edge.toFareyCellPacket.G -
        (M.actual.q : ℤ) - C.cellCost := by
  have h := C.actualQ_add_cellCost_lt_gap
  omega

/-- selected cell cost の local exact identity。 -/
theorem twoPow_mul_cellCost_eq_gap_mul_localInverse_add_threePow
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    (2 : ℤ) ^ C.step.edge.fareyTailDepth * C.cellCost =
      C.step.edge.toFareyCellPacket.G *
          (C.step.edge.fareyLocalInverse : ℤ) +
        (3 : ℤ) ^ C.step.edge.fareyRightExponent := by
  exact
    C.step.edge.twoPow_mul_fareyCellCost_eq_gap_mul_fareyLocalInverse_add_threePow

/-- selected cell cost の full-scale exact identity。 -/
theorem twoPow_length_mul_cellCost_eq_gap_mul_deltaR_add_deltaB
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    (2 : ℤ) ^ C.step.edge.length * C.cellCost =
      C.step.edge.toFareyCellPacket.G * (C.step.edge.deltaR : ℤ) +
        (C.step.edge.deltaB : ℤ) := by
  exact
    C.step.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB

end BoundaryRespectingPredecessorCell
end MinimalActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
