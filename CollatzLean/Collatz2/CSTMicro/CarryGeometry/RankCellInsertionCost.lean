import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersStepRankTransport

/-!
# Ferrers rank-cell insertion cost

Step 1--3 で得た

* upper cell の `3 * fareyCellCost = inverseRankWeight(rankCut)`,
* selected cut の rank quotient が lower から upper へ exact に 1 増えること

を結合する。

lower quotient を `q` とすると、upper inverse rank weight は

  baseResidueWeight * halfUnitValue^(q+1)

である。一方 Ferrers cell sum に新しく追加される一セルは

  baseResidueWeight * halfUnitValue^q.

`halfUnitValue * 2 = 1` なので、一セルの integer cost の modular image は

  6 * fareyCellCost = inserted rank-cell weight

となる。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersStep

/-- selected rank column に一つ追加される Ferrers cell の weight。 -/
noncomputable def rankCellInsertionWeight
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (R : Collatz2.Word.RankUnitData S.edge.rankUpperExponentWord) :
    ZMod (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord) :=
  Collatz2.Word.baseResidueWeight R S.edge.rankCut *
    Collatz2.Word.halfUnitValue R ^
      Collatz2.Word.rankQuotient S.edge.rankLowerExponentWord S.edge.rankCut

/--
upper inverse rank weight は、追加された cell weight に half-unit を一回掛けたもの。
-/
theorem inverseRankWeight_eq_halfUnitValue_mul_rankCellInsertionWeight
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (R : Collatz2.Word.RankUnitData S.edge.rankUpperExponentWord) :
    Collatz2.Word.inverseRankWeight R S.edge.rankCut =
      Collatz2.Word.halfUnitValue R * S.rankCellInsertionWeight R := by
  rw [R.inverseRankWeight_eq_baseResidueWeight_mul_halfUnitValue_pow]
  rw [S.rankQuotient_upper_eq_lower_add_one_at_rankCut hLowerFP]
  unfold rankCellInsertionWeight
  rw [pow_succ]
  ring

/--
selected column の geometric Ferrers sum は、一 step で insertion weight だけ増える。
-/
theorem selectedFerrersColumn_upper_eq_lower_add_insertionWeight
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (R : Collatz2.Word.RankUnitData S.edge.rankUpperExponentWord) :
    Collatz2.Word.baseResidueWeight R S.edge.rankCut *
        Collatz2.Word.halfCellColumnSum R
          (Collatz2.Word.rankQuotient
            S.edge.rankUpperExponentWord S.edge.rankCut) =
      Collatz2.Word.baseResidueWeight R S.edge.rankCut *
          Collatz2.Word.halfCellColumnSum R
            (Collatz2.Word.rankQuotient
              S.edge.rankLowerExponentWord S.edge.rankCut) +
        S.rankCellInsertionWeight R := by
  have hQ := S.rankQuotient_upper_eq_lower_add_one_at_rankCut hLowerFP
  rw [hQ]
  unfold Collatz2.Word.halfCellColumnSum rankCellInsertionWeight
  rw [Finset.sum_range_succ]
  ring

/--
一つの first-passage Ferrers step で、positive integer cell cost の6倍は
新しく追加される rank Ferrers cell weight に exact に一致する。
-/
theorem six_mul_fareyCellCost_cast_eq_rankCellInsertionWeight
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (R : Collatz2.Word.RankUnitData S.edge.rankUpperExponentWord) :
    (6 : ZMod (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)) *
        (S.edge.fareyCellCost :
          ZMod (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)) =
      S.rankCellInsertionWeight R := by
  let G := Collatz2.Word.terminalGap S.edge.rankUpperExponentWord
  have hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hBridgeRaw :=
    S.edge.three_mul_fareyCellCost_cast_eq_inverseRankWeight hUpperFP R
  have hBridge :
      (3 : ZMod G) * (S.edge.fareyCellCost : ZMod G) =
        Collatz2.Word.inverseRankWeight R S.edge.rankCut := by
    simpa [G] using hBridgeRaw
  have hFactor :=
    S.inverseRankWeight_eq_halfUnitValue_mul_rankCellInsertionWeight hLowerFP R
  have hHalfRaw := R.halfUnitValue_mul_two_eq_one
  have hHalf :
      (2 : ZMod G) * Collatz2.Word.halfUnitValue R = 1 := by
    simpa [G, mul_comm] using hHalfRaw
  calc
    (6 : ZMod G) * (S.edge.fareyCellCost : ZMod G)
        = (2 : ZMod G) *
            ((3 : ZMod G) * (S.edge.fareyCellCost : ZMod G)) := by
              ring
    _ = (2 : ZMod G) *
          Collatz2.Word.inverseRankWeight R S.edge.rankCut := by
            rw [hBridge]
    _ = (2 : ZMod G) *
          (Collatz2.Word.halfUnitValue R * S.rankCellInsertionWeight R) := by
            rw [hFactor]
    _ =
      ((2 : ZMod G) * Collatz2.Word.halfUnitValue R) *
        S.rankCellInsertionWeight R := by
          ring
    _ = S.rankCellInsertionWeight R := by
          rw [hHalf]
          ring

/-- primitive endpoint では rank unit も内部構成できる。 -/
theorem exists_rankUnit_six_mul_fareyCellCost_eq_insertionWeight_of_coprime
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hcop : Nat.Coprime S.edge.length S.edge.oddTotal) :
    ∃ R : Collatz2.Word.RankUnitData S.edge.rankUpperExponentWord,
      (6 : ZMod (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)) *
          (S.edge.fareyCellCost :
            ZMod (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)) =
        S.rankCellInsertionWeight R := by
  have hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hF := S.edge.rankUpperExponentWord_firstCrossing hUpperFP
  have hcopWord :
      Nat.Coprime
        (Collatz2.Word.twoSteps S.edge.rankUpperExponentWord)
        (Collatz2.Word.oddSteps S.edge.rankUpperExponentWord) := by
    rw [S.edge.rankUpperExponentWord_twoSteps hUpperFP]
    rw [S.edge.rankUpperExponentWord_oddSteps]
    exact hcop
  obtain ⟨R⟩ := hF.exists_rankUnitData_of_coprime hcopWord
  exact
    ⟨R, S.six_mul_fareyCellCost_cast_eq_rankCellInsertionWeight hLowerFP R⟩

end FerrersStep

end CSTMicro
end Collatz2
