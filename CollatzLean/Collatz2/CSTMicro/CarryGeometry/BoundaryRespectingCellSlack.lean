import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadCellCostObstruction

/-!
# Boundary-respecting predecessor cell slack

`BoundaryRespectingPredecessorCell` は minimal bad word `B` の直前にあり、
その predecessor 自身も first-passage である。

selected cell の座標を

  i = swap position,
  a = upper prefix odd count at i+1,
  d = k-i,
  r = m-a

とすると、predecessor 側では同じ prefix `i+1` に odd がまだ移動していないため
height は `a-1`。

predecessor も proper-prefix expanding なので

  2^(i+1) < 3^(a-1).

terminal contraction と合わせると

  6 * 3^r < 2^d,

さらに full scale では

  6 * deltaB < 2^k.

これは boundary-respecting exposed cell が単なる任意の Farey cell ではなく、
一段分の genuine first-passage slack を持つことを整数だけで表す。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket
namespace BoundaryRespectingPredecessorCell

/-- selected cell の upper height `a` は正。 -/
theorem a_pos
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    0 < C.a := by
  rw [C.a_eq_leftOdd_succ]
  omega

/-- selected cell の prefix index `i+1` は word の proper prefix。 -/
theorem i_succ_lt_length
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.i + 1 < C.pred.length := by
  have hPos :
      C.step.edge.position + 1 <
        C.step.edge.length := by
    unfold AdjacentFerrersSwap.position
      AdjacentFerrersSwap.length
    omega
  have hEdgeLen :
      C.step.edge.length =
        C.step.edge.lowerWord.length := by
    exact C.step.edge.lowerWord_length.symm
  have hLower :
      C.pred.length =
        C.step.edge.lowerWord.length :=
    congrArg List.length C.step.lower_eq
  calc
    C.i + 1
        =
      C.step.edge.position + 1 := by
        rw [C.i_eq_position]
    _ < C.step.edge.length :=
      hPos
    _ = C.step.edge.lowerWord.length :=
      hEdgeLen
    _ = C.pred.length :=
      hLower.symm

/-- predecessor 側の selected prefix height は exact に `a-1`。 -/
theorem pred_prefixOddCount_at_selectedCell
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    prefixOddCount C.pred (C.i + 1) = C.a - 1 := by
  have hCell := C.step.edge.lower_prefixOddCount_at_cell
  rw [← C.step.lower_eq] at hCell
  rw [← C.i_eq_position, ← C.a_eq_leftExponent] at hCell
  have ha := C.a_pos
  omega

/--
selected predecessor は first-passage なので、一段遅らせた height `a-1` のままでも expanding。

  2^(i+1) < 3^(a-1).
-/
theorem oneStepFirstPassageSlack
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    2 ^ (C.i + 1) < 3 ^ (C.a - 1) := by
  have hExp :=
    C.pred_firstPassage.2.1
      (C.i + 1)
      (by omega)
      C.i_succ_lt_length
  unfold CoefficientExpandingAt at hExp
  rw [C.pred_prefixOddCount_at_selectedCell] at hExp
  exact hExp

/-- selected cell の tail depth decomposition `k=i+d`。 -/
theorem length_eq_i_add_tailDepth
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.step.edge.length = C.i + C.step.edge.fareyTailDepth := by
  rw [C.i_eq_position]
  exact C.step.edge.length_eq_position_add_fareyTailDepth

/-- selected cell の odd decomposition `m=a+r`。 -/
theorem oddTotal_eq_a_add_rightExponent
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.step.edge.oddTotal = C.a + C.step.edge.fareyRightExponent := by
  rw [C.a_eq_leftExponent]
  exact C.step.edge.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent

/-- selected cell の upper/whole first-passage contraction。 -/
theorem terminalContractingPow
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    3 ^ C.step.edge.oddTotal < 2 ^ C.step.edge.length := by
  have h := M.word_firstPassage.2.2
  unfold CoefficientContracting at h
  have hOdd :
      oddCount M.word = C.step.edge.oddTotal := by
    calc
      oddCount M.word
          = oddCount C.step.edge.upperWord :=
            congrArg oddCount C.step.upper_eq
      _ = C.step.edge.oddTotal :=
            C.step.edge.upperWord_oddCount
  have hLen :
      M.word.length = C.step.edge.length := by
    calc
      M.word.length
          = C.step.edge.upperWord.length :=
            congrArg List.length C.step.upper_eq
      _ = C.step.edge.length :=
            C.step.edge.upperWord_length
  rw [hOdd, hLen] at h
  exact h

/--
一段の predecessor slack と terminal contraction を tail coordinates に移す。

  6 * 3^r < 2^d.
-/
theorem six_mul_threePow_rightExponent_lt_twoPow_tailDepth
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    6 * 3 ^ C.step.edge.fareyRightExponent <
      2 ^ C.step.edge.fareyTailDepth := by
  have hSlack := C.oneStepFirstPassageSlack
  have hContract := C.terminalContractingPow
  have hLen := C.length_eq_i_add_tailDepth
  have hOdd := C.oddTotal_eq_a_add_rightExponent
  have hAux :
      2 ^ (C.i + 1) *
          3 ^ (C.step.edge.fareyRightExponent + 1) <
        3 ^ (C.a - 1) *
          3 ^ (C.step.edge.fareyRightExponent + 1) :=
    Nat.mul_lt_mul_of_pos_right hSlack (by positivity)
  have hExp :
      (C.a - 1) +
          (C.step.edge.fareyRightExponent + 1) =
        C.a + C.step.edge.fareyRightExponent := by
    have ha := C.a_pos
    omega
  have hMid :
      2 ^ (C.i + 1) *
          3 ^ (C.step.edge.fareyRightExponent + 1) <
        2 ^ (C.i + C.step.edge.fareyTailDepth) := by
    calc
      2 ^ (C.i + 1) *
            3 ^ (C.step.edge.fareyRightExponent + 1)
          <
        3 ^ (C.a - 1) *
            3 ^ (C.step.edge.fareyRightExponent + 1) :=
        hAux
      _ =
        3 ^ (C.a + C.step.edge.fareyRightExponent) := by
          rw [← pow_add]
          rw [hExp]
      _ =
        3 ^ C.step.edge.oddTotal := by
          rw [hOdd]
      _ <
        2 ^ C.step.edge.length :=
        hContract
      _ =
        2 ^ (C.i + C.step.edge.fareyTailDepth) := by
          rw [hLen]
  have hFactor :
      2 ^ C.i *
          (6 * 3 ^ C.step.edge.fareyRightExponent) <
        2 ^ C.i *
          2 ^ C.step.edge.fareyTailDepth := by
    calc
      2 ^ C.i *
            (6 * 3 ^ C.step.edge.fareyRightExponent)
          =
        2 ^ (C.i + 1) *
            3 ^ (C.step.edge.fareyRightExponent + 1) := by
          rw [pow_add, pow_add]
          norm_num
          ring
      _ <
        2 ^ (C.i + C.step.edge.fareyTailDepth) :=
        hMid
      _ =
        2 ^ C.i *
          2 ^ C.step.edge.fareyTailDepth := by
          rw [pow_add]
  exact Nat.lt_of_mul_lt_mul_left hFactor

/-- full-scale affine decrement は modulus の 1/6 より strict に小さい。 -/
theorem six_mul_deltaB_lt_modulus
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    6 * C.step.edge.deltaB < C.step.edge.modulus := by
  have hTail := C.six_mul_threePow_rightExponent_lt_twoPow_tailDepth
  unfold AdjacentFerrersSwap.deltaB AdjacentFerrersSwap.modulus
  rw [C.step.edge.length_eq_position_add_fareyTailDepth, pow_add]
  have hp : 0 < 2 ^ C.step.edge.position := Nat.pow_pos (by omega)
  calc
    6 * (2 ^ C.step.edge.position *
        3 ^ C.step.edge.fareyRightExponent)
        =
      2 ^ C.step.edge.position *
        (6 * 3 ^ C.step.edge.fareyRightExponent) := by ring
    _ <
      2 ^ C.step.edge.position *
        2 ^ C.step.edge.fareyTailDepth :=
          (Nat.mul_lt_mul_left hp).2 hTail

/--
selected cell の現在分かっている情報を lossless に一 packet にまとめる。
-/
structure CostSlackPacket
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) where
  cost : ℤ
  cost_eq : cost = C.cellCost
  cost_pos : 0 < cost
  q_add_cost_lt_gap :
    (M.actual.q : ℤ) + cost < C.step.edge.toFareyCellPacket.G
  cost_local_exact :
    (2 : ℤ) ^ C.step.edge.fareyTailDepth * cost =
      C.step.edge.toFareyCellPacket.G *
          (C.step.edge.fareyLocalInverse : ℤ) +
        (3 : ℤ) ^ C.step.edge.fareyRightExponent
  cost_full_exact :
    (2 : ℤ) ^ C.step.edge.length * cost =
      C.step.edge.toFareyCellPacket.G * (C.step.edge.deltaR : ℤ) +
        (C.step.edge.deltaB : ℤ)
  one_step_slack : 2 ^ (C.i + 1) < 3 ^ (C.a - 1)
  tail_six_gap :
    6 * 3 ^ C.step.edge.fareyRightExponent <
      2 ^ C.step.edge.fareyTailDepth
  deltaB_six_gap :
    6 * C.step.edge.deltaB < C.step.edge.modulus

/-- selected boundary-respecting cell から canonical cost/slack packet を構成。 -/
def toCostSlackPacket
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    CostSlackPacket C := {
  cost := C.cellCost
  cost_eq := rfl
  cost_pos := C.cellCost_pos
  q_add_cost_lt_gap := C.actualQ_add_cellCost_lt_gap
  cost_local_exact := C.twoPow_mul_cellCost_eq_gap_mul_localInverse_add_threePow
  cost_full_exact := C.twoPow_length_mul_cellCost_eq_gap_mul_deltaR_add_deltaB
  one_step_slack := C.oneStepFirstPassageSlack
  tail_six_gap := C.six_mul_threePow_rightExponent_lt_twoPow_tailDepth
  deltaB_six_gap := C.six_mul_deltaB_lt_modulus
}

end BoundaryRespectingPredecessorCell
end MinimalActualABObstructionPacket
end ExternalArithmetic
end CSTMicro
end Collatz2
