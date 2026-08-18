import CollatzLean.Collatz2.CSTMicro.CarryGeometry.GeneralPredecessorRankCellBridge

/-!
# First-passage predecessor -> positive rank depth

一般 adjacent rank bridge に predecessor の first-passage 条件を加える。
lower word の cell prefix `position+1` では odd がまだ一段右にあるため、

  2^(position+1) < 3^rankCut

が成り立つ。upper 側では同じ rankCut checkpoint が exact に `position` なので、
critical roof から少なくとも一層沈み

  extraDepth >= 1,
  rankQuotient > 0

を得る。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersStep

/-- lower first-passage edge の selected standard prefix は proper。 -/
theorem rankCell_position_succ_lt_lower_length
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.edge.position + 1 < lower.length := by
  have hPos : S.edge.position + 1 < S.edge.length := by
    unfold AdjacentFerrersSwap.position AdjacentFerrersSwap.length
    omega
  calc
    S.edge.position + 1 < S.edge.length := hPos
    _ = S.edge.lowerWord.length := S.edge.lowerWord_length.symm
    _ = lower.length := congrArg List.length S.lower_eq.symm

/-- lower side では selected prefix の odd count は rankCut そのもの。 -/
theorem lower_prefixOddCount_at_rankCell
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    prefixOddCount lower (S.edge.position + 1) = S.edge.rankCut := by
  have hCell := S.edge.lower_prefixOddCount_at_cell
  have hEdge :
      prefixOddCount S.edge.lowerWord (S.edge.position + 1) =
        S.edge.rankCut := by
    unfold AdjacentFerrersSwap.fareyLeftExponent at hCell
    unfold AdjacentFerrersSwap.rankCut
    omega
  calc
    prefixOddCount lower (S.edge.position + 1)
        =
      prefixOddCount S.edge.lowerWord (S.edge.position + 1) :=
        congrArg
          (fun v : ParityWord =>
            prefixOddCount v (S.edge.position + 1))
          S.lower_eq
    _ = S.edge.rankCut := hEdge

/--
first-passage predecessor の one-step slack。

  2^(position+1) < 3^rankCut.
-/
theorem rankCell_oneStepFirstPassageSlack
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    2 ^ (S.edge.position + 1) < 3 ^ S.edge.rankCut := by
  have hExp :=
    hLowerFP.2.1
      (S.edge.position + 1)
      (by omega)
      S.rankCell_position_succ_lt_lower_length
  unfold CoefficientExpandingAt at hExp
  rw [S.lower_prefixOddCount_at_rankCell] at hExp
  exact hExp

/-- first-passage predecessor では selected odd cut は正。 -/
theorem rankCell_cut_pos
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < S.edge.rankCut := by
  have hSlack := S.rankCell_oneStepFirstPassageSlack hLowerFP
  by_contra hnot
  have hk : S.edge.rankCut = 0 := by omega
  rw [hk, pow_zero] at hSlack
  have hPos : 0 < 2 ^ (S.edge.position + 1) := by positivity
  omega

/-- lower first-passage は upper first-passage を保つ。 -/
theorem edge_upper_firstPassage_of_lower
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    IsFirstPassageWord S.edge.upperWord := by
  have hUpperFP : IsFirstPassageWord upper :=
    S.preserves_firstPassage hLowerFP
  have hEq :
      IsFirstPassageWord upper =
        IsFirstPassageWord S.edge.upperWord :=
    congrArg IsFirstPassageWord S.upper_eq
  exact Eq.mp hEq hUpperFP

/--
selected upper rank cut は critical roof から少なくとも一層沈む。
-/
theorem one_le_extraDepth_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    1 ≤ Collatz2.Word.extraDepth
      S.edge.rankUpperExponentWord S.edge.rankCut := by
  have hSlack := S.rankCell_oneStepFirstPassageSlack hLowerFP
  have hCrit :
      S.edge.position + 1 ≤ Collatz2.Word.criticalHeight S.edge.rankCut :=
    Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hSlack
  have hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  unfold Collatz2.Word.extraDepth
  rw [S.edge.prefixTwoDepth_rankCut_eq_position hUpperFP]
  omega

/-- selected cut は genuine positive Ferrers rank column を持つ。 -/
theorem rankQuotient_rankCut_pos
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < Collatz2.Word.rankQuotient
      S.edge.rankUpperExponentWord S.edge.rankCut := by
  have hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hF := S.edge.rankUpperExponentWord_firstCrossing hUpperFP
  have hEq :=
    hF.rankQuotient_eq_stripDiv_add_extraDepth
      (S.rankCell_cut_pos hLowerFP)
      S.edge.rankCut_lt_oddSteps
  rw [hEq]
  have hExtra := S.one_le_extraDepth_rankCut hLowerFP
  have hExtraPos :
      0 < Collatz2.Word.extraDepth
        S.edge.rankUpperExponentWord S.edge.rankCut := by
    omega
  positivity

end FerrersStep

end CSTMicro
end Collatz2
