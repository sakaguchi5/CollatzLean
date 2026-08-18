import CollatzLean.Collatz2.CSTMicro.CarryGeometry.BoundaryRespectingCellSlack
import CollatzLean.Collatz2.Geometry.WeightedRankFerrers

set_option linter.style.longLine false

/-!
# Boundary-respecting micro cell -> odd-only rank cell

minimal bad B の boundary-respecting predecessor cell `(i,a)` を、B の odd-only exponent word の
proper cut

  t = a - 1

へ exact に戻す。

run encoder について一般に、`p ++ true :: rest` の直前までにある odd 数 `oddCount p` を
読み終えた checkpoint は exact に `p.length` である。これを selected cell に適用すると

  prefixTwoDepth(w,t) = i.

predecessor の one-step first-passage slack

  2^(i+1) < 3^t

から

  extraDepth(w,t) >= 1

を得る。さらに cell cost full-scale identity を mod terminal gap に落とし、既存
weighted-rank cut certificate と結合すると、任意の `RankUnitData` に対し

  3 * cellCost = inverseRankWeight(t)       (mod G)

となる。primitive `(H,p)=1` では rank unit は内部構成できる。
-/

namespace Collatz2
namespace CSTMicro

/--
`p` の直後が odd bit なら、run encoder の `oddCount p` checkpoint は exact に `p.length`。
leading even-run も含めた一般形。
-/
theorem leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
    (p rest : ParityWord) :
    leadingEvenCount (p ++ true :: rest) +
        Collatz2.Word.twoSteps
          ((exponentWordOfParity (p ++ true :: rest)).take (oddCount p)) =
      p.length := by
  induction p generalizing rest with
  | nil =>
      simp [oddCount]
  | cons b p ih =>
      cases b
      · have hih := ih rest
        simp only [
          List.cons_append,
          leadingEvenCount_false_cons,
          exponentWordOfParity_false_cons,
          oddCount_false_cons,
          List.length_cons
        ]
        omega
      · have hih := ih rest
        simp only [
          List.cons_append,
          leadingEvenCount_true_cons,
          exponentWordOfParity_true_cons,
          oddCount_true_cons,
          List.length_cons,
          List.take_succ_cons,
          Collatz2.Word.twoSteps_cons,
          zero_add
        ]
        omega

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket
namespace BoundaryRespectingPredecessorCell

/-- selected exposed cell に対応する odd-only proper cut。 -/
def oddCut
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) : ℕ :=
  C.a - 1

/-- selected B upper word の odd-only exponent encoding。 -/
def selectedExponentWord
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) : Collatz2.Word :=
  exponentWordOfParity C.step.edge.upperWord

/-- `t=a-1` は leftContext 内の odd 数そのもの。 -/
theorem oddCut_eq_leftOdd
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.oddCut = oddCount C.step.edge.leftContext := by
  unfold oddCut
  rw [C.a_eq_leftOdd_succ]
  omega

/-- selected cut は正。 -/
theorem oddCut_pos
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    0 < C.oddCut := by
  have hSlack := C.oneStepFirstPassageSlack
  by_contra hnot
  have ht : C.a - 1 = 0 := by
    unfold oddCut at hnot
    omega
  rw [ht, pow_zero] at hSlack
  have hPos : 0 < 2 ^ (C.i + 1) := by positivity
  omega

/-- encoded odd step 数は selected edge の total odd count。 -/
@[simp] theorem selectedExponentWord_oddSteps
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    Collatz2.Word.oddSteps C.selectedExponentWord = C.step.edge.oddTotal := by
  unfold selectedExponentWord
  rw [oddSteps_exponentWordOfParity]
  exact C.step.edge.upperWord_oddCount

/-- selected cut は proper cut。 -/
theorem oddCut_lt_oddSteps
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    C.oddCut < Collatz2.Word.oddSteps C.selectedExponentWord := by
  rw [C.selectedExponentWord_oddSteps]
  have hOdd := C.oddTotal_eq_a_add_rightExponent
  have ha := C.a_pos
  unfold oddCut
  omega

/-- selected exponent word の leading even-run は zero。 -/
theorem selected_leadingEvenCount_eq_zero
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    leadingEvenCount C.step.edge.upperWord = 0 := by
  have h := C.firstFailureEdge.leadingEvenCount_edge_upperWord_eq_zero
  change leadingEvenCount C.step.edge.upperWord = 0 at h
  exact h

/--
selected cell の standard position `i` は odd-only cut `t=a-1` の exact two-depth checkpoint。
-/
theorem prefixTwoDepth_oddCut_eq_i
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    Collatz2.Word.prefixTwoDepth C.selectedExponentWord C.oddCut = C.i := by
  have hRun :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
      C.step.edge.leftContext
      (false :: C.step.edge.rightContext)
  change
    leadingEvenCount C.step.edge.upperWord +
        Collatz2.Word.twoSteps
          ((exponentWordOfParity C.step.edge.upperWord).take
            (oddCount C.step.edge.leftContext)) =
      C.step.edge.leftContext.length at hRun
  rw [C.selected_leadingEvenCount_eq_zero, zero_add] at hRun
  unfold Collatz2.Word.prefixTwoDepth selectedExponentWord
  rw [C.oddCut_eq_leftOdd, C.i_eq_leftLength]
  exact hRun

/-- selected exponent word は既存 B first-failure FirstCrossing word と同じ。 -/
theorem selectedExponentWord_firstCrossing
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    Collatz2.Word.FirstCrossing C.selectedExponentWord := by
  have h := C.firstFailureEdge.upperExponentWord_firstCrossing
  change Collatz2.Word.FirstCrossing
    (exponentWordOfParity C.step.edge.upperWord) at h
  exact h

/-- selected exponent word の total two-depth は standard length。 -/
@[simp] theorem selectedExponentWord_twoSteps
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    Collatz2.Word.twoSteps C.selectedExponentWord = C.step.edge.length := by
  have h := C.firstFailureEdge.upperExponentWord_twoSteps
  change
    Collatz2.Word.twoSteps (exponentWordOfParity C.step.edge.upperWord) =
      C.step.edge.length at h
  exact h

/-- one-step slack により selected cut は critical roof から少なくとも一層沈む。 -/
theorem one_le_extraDepth_oddCut
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    1 ≤ Collatz2.Word.extraDepth C.selectedExponentWord C.oddCut := by
  have hSlack :
      2 ^ (C.i + 1) < 3 ^ C.oddCut := by
    simpa [oddCut] using C.oneStepFirstPassageSlack
  have hCrit :
      C.i + 1 ≤ Collatz2.Word.criticalHeight C.oddCut :=
    Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hSlack
  unfold Collatz2.Word.extraDepth
  rw [C.prefixTwoDepth_oddCut_eq_i]
  omega

/-- selected cut は rank quotient 側でも genuine positive Ferrers column を持つ。 -/
theorem rankQuotient_oddCut_pos
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    0 < Collatz2.Word.rankQuotient C.selectedExponentWord C.oddCut := by
  have hF := C.selectedExponentWord_firstCrossing
  have hEq :=
    hF.rankQuotient_eq_stripDiv_add_extraDepth
      C.oddCut_pos C.oddCut_lt_oddSteps
  rw [hEq]
  have hExtra := C.one_le_extraDepth_oddCut
  have hExtraPos :
      0 < Collatz2.Word.extraDepth C.selectedExponentWord C.oddCut := by
    omega
  positivity

/-- selected normalized cut term は exact に `3 * deltaB`。 -/
theorem normalizedCutTerm_oddCut_eq_three_mul_deltaB
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    Collatz2.Word.normalizedCutTerm C.selectedExponentWord C.oddCut =
      3 * C.step.edge.deltaB := by
  have hOdd := C.oddTotal_eq_a_add_rightExponent
  have ha := C.a_pos
  have hSub :
      C.step.edge.oddTotal - C.oddCut =
        C.step.edge.fareyRightExponent + 1 := by
    unfold oddCut
    omega
  unfold Collatz2.Word.normalizedCutTerm
  rw [C.prefixTwoDepth_oddCut_eq_i]
  rw [C.selectedExponentWord_oddSteps, hSub]
  unfold AdjacentFerrersSwap.deltaB AdjacentFerrersSwap.fareyRightExponent
  rw [← C.i_eq_position, pow_succ]
  ring_nf

/-- selected exponent word の terminal gap cast は local Farey `G`。 -/
theorem terminalGap_cast_eq_fareyG
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) :
    (Collatz2.Word.terminalGap C.selectedExponentWord : ℤ) =
      C.step.edge.toFareyCellPacket.G := by
  have hContract := C.terminalContractingPow
  unfold Collatz2.Word.terminalGap
  rw [C.selectedExponentWord_twoSteps, C.selectedExponentWord_oddSteps]
  rw [Nat.cast_sub (Nat.le_of_lt hContract)]
  change
    (2 : ℤ) ^ C.step.edge.length - (3 : ℤ) ^ C.step.edge.oddTotal =
      C.step.edge.toFareyCellPacket.G
  rfl

/--
selected cell cost の mod-G image は既存 inverse rank weight と exact に同じ cell を表す。

  3 * cellCost = inverseRankWeight(t)  (mod G).
-/
theorem three_mul_cellCost_cast_eq_inverseRankWeight
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M)
    (R : Collatz2.Word.RankUnitData C.selectedExponentWord) :
    ((3 : ℤ) : ZMod (Collatz2.Word.terminalGap C.selectedExponentWord)) *
        (C.cellCost : ZMod (Collatz2.Word.terminalGap C.selectedExponentWord)) =
      Collatz2.Word.inverseRankWeight R C.oddCut := by
  let w := C.selectedExponentWord
  let G := Collatz2.Word.terminalGap w
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using C.selectedExponentWord_firstCrossing
  have hFull := C.twoPow_length_mul_cellCost_eq_gap_mul_deltaR_add_deltaB
  have hGapInt : C.step.edge.toFareyCellPacket.G = (G : ℤ) := by
    dsimp [G, w]
    exact C.terminalGap_cast_eq_fareyG.symm
  have hCast := congrArg (fun z : ℤ => (z : ZMod G)) hFull
  push_cast at hCast
  have hGapZero :
      ((C.step.edge.toFareyCellPacket.G : ℤ) : ZMod G) = 0 := by
    rw [hGapInt]
    simp
  rw [hGapZero, zero_mul, zero_add] at hCast
  have hLength : C.step.edge.length = Collatz2.Word.twoSteps w := by
    simp only [selectedExponentWord_twoSteps, w]
  rw [hLength] at hCast
  have hCastNat :
      (((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
          (C.cellCost : ZMod G) =
        ((C.step.edge.deltaB : ℕ) : ZMod G) := by
    push_cast
    exact hCast
  have hPow :
      (((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) := by
    change
      (((2 ^ Collatz2.Word.twoSteps C.firstFailureEdge.upperExponentWord : ℕ)) :
          ZMod (Collatz2.Word.terminalGap C.firstFailureEdge.upperExponentWord)) =
        (((3 ^ Collatz2.Word.oddSteps C.firstFailureEdge.upperExponentWord : ℕ)) :
          ZMod (Collatz2.Word.terminalGap C.firstFailureEdge.upperExponentWord))
    exact C.firstFailureEdge.upperExponentWord_twoPow_cast_eq_threePow_cast
  have hTermNat := C.normalizedCutTerm_oddCut_eq_three_mul_deltaB
  have hTermCast :
      ((Collatz2.Word.normalizedCutTerm w C.oddCut : ℕ) : ZMod G) =
        (((3 * C.step.edge.deltaB : ℕ)) : ZMod G) := by
    exact congrArg (fun n : ℕ => (n : ZMod G)) hTermNat
  have hScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          (((3 : ℤ) : ZMod G) * (C.cellCost : ZMod G)) =
        ((Collatz2.Word.normalizedCutTerm w C.oddCut : ℕ) : ZMod G) := by
    calc
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
            (((3 : ℤ) : ZMod G) * (C.cellCost : ZMod G))
          =
        (((3 : ℤ) : ZMod G) *
          ((((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
            (C.cellCost : ZMod G))) := by
              rw [hPow]
              ring
      _ =
        (((3 : ℤ) : ZMod G) *
          ((C.step.edge.deltaB : ℕ) : ZMod G)) := by
            rw [hCastNat]
      _ = (((3 * C.step.edge.deltaB : ℕ)) : ZMod G) := by
            push_cast
            ring
      _ = ((Collatz2.Word.normalizedCutTerm w C.oddCut : ℕ) : ZMod G) :=
            hTermCast.symm
  have hCert :=
    R.normalizedCutTerm_eq_threePow_mul_inverseRankWeight
      hF C.oddCut_lt_oddSteps
  have hEq :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          (((3 : ℤ) : ZMod G) * (C.cellCost : ZMod G)) =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          Collatz2.Word.inverseRankWeight R C.oddCut := by
    exact hScaled.trans hCert
  exact R.cancel_threePow hEq

/-- primitive endpoint では selected cell の rank unit / cost identity を内部構成できる。 -/
structure PrimitiveCellRankPacket
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M) where
  rankUnit : Collatz2.Word.RankUnitData C.selectedExponentWord
  cost_rank :
    ((3 : ℤ) : ZMod (Collatz2.Word.terminalGap C.selectedExponentWord)) *
        (C.cellCost : ZMod (Collatz2.Word.terminalGap C.selectedExponentWord)) =
      Collatz2.Word.inverseRankWeight rankUnit C.oddCut

/-- coprime `(H,p)` なら primitive selected-cell rank packet が存在する。 -/
theorem exists_primitiveCellRankPacket_of_coprime
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    (C : BoundaryRespectingPredecessorCell M)
    (hcop : Nat.Coprime
      (Collatz2.Word.twoSteps C.selectedExponentWord)
      (Collatz2.Word.oddSteps C.selectedExponentWord)) :
    Nonempty (PrimitiveCellRankPacket C) := by
  have hF := C.selectedExponentWord_firstCrossing
  rcases hF.exists_rankUnitData_of_coprime hcop with ⟨R⟩
  exact
    ⟨{
      rankUnit := R
      cost_rank := C.three_mul_cellCost_cast_eq_inverseRankWeight R
    }⟩

end BoundaryRespectingPredecessorCell
end MinimalActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
