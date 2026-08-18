import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FirstPassagePredecessorRankDepth

set_option linter.style.longLine false

/-!
# Ferrers step rank transport

first-passage Ferrers step `01 -> 10` を odd-only rank geometry へ直接移す。
cell cut `t = oddCount(leftContext)` では

  prefixTwoDepth(lower,t) = position + 1,
  prefixTwoDepth(upper,t) = position,

なので chord rank は exact に oddTotal だけ増える。従って

  rankResidue(upper,t) = rankResidue(lower,t),
  rankQuotient(upper,t) = rankQuotient(lower,t) + 1.

また standard prefix-height は swap column 以外では不変である。
-/

namespace Collatz2
namespace CSTMicro

/-- `p ++ 01 ++ rest` の selected run checkpoint は `p.length + 1`。 -/
theorem leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_succ_before_false_true
    (p rest : ParityWord) :
    leadingEvenCount (p ++ false :: true :: rest) +
        Collatz2.Word.twoSteps
          ((exponentWordOfParity (p ++ false :: true :: rest)).take (oddCount p)) =
      p.length + 1 := by
  have h :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
      (p ++ [false]) rest
  simpa [List.append_assoc, cstOddCount_append, oddCount, bitNat] using h

namespace AdjacentFerrersSwap

/-- lower parity word の odd-only run encoding。 -/
def rankLowerExponentWord (S : AdjacentFerrersSwap) : Collatz2.Word :=
  exponentWordOfParity S.lowerWord

/-- lower encoded odd count も common odd total。 -/
@[simp] theorem rankLowerExponentWord_oddSteps
    (S : AdjacentFerrersSwap) :
    Collatz2.Word.oddSteps S.rankLowerExponentWord = S.oddTotal := by
  unfold rankLowerExponentWord
  rw [oddSteps_exponentWordOfParity]
  exact S.lowerWord_oddCount

/-- lower word も構造上 length >= 2。 -/
theorem one_lt_rankLowerWord_length (S : AdjacentFerrersSwap) :
    1 < S.lowerWord.length := by
  rw [S.lowerWord_length]
  unfold AdjacentFerrersSwap.length
  omega

/-- lower first-passage なら encoded two-depth は common length。 -/
@[simp] theorem rankLowerExponentWord_twoSteps
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.twoSteps S.rankLowerExponentWord = S.length := by
  unfold rankLowerExponentWord
  calc
    Collatz2.Word.twoSteps (exponentWordOfParity S.lowerWord)
        = S.lowerWord.length :=
      hLowerFP.twoSteps_exponentWordOfParity_eq_length S.one_lt_rankLowerWord_length
    _ = S.length := S.lowerWord_length

/-- lower first-passage なら encoded lower も FirstCrossing。 -/
theorem rankLowerExponentWord_firstCrossing
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.FirstCrossing S.rankLowerExponentWord := by
  unfold rankLowerExponentWord
  exact hLowerFP.exponentWordOfParity_firstCrossing S.one_lt_rankLowerWord_length

/-- lower first-passage なら leading even-run は zero。 -/
theorem rankLower_leadingEvenCount_eq_zero
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    leadingEvenCount S.lowerWord = 0 :=
  hLowerFP.leadingEvenCount_eq_zero_of_one_lt_length S.one_lt_rankLowerWord_length

/--
lower `01` cell の同じ odd cut checkpoint は position+1。
-/
theorem prefixTwoDepth_rankCut_eq_position_add_one
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.prefixTwoDepth S.rankLowerExponentWord S.rankCut =
      S.position + 1 := by
  have hRun :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_succ_before_false_true
      S.leftContext S.rightContext
  change
    leadingEvenCount S.lowerWord +
        Collatz2.Word.twoSteps
          ((exponentWordOfParity S.lowerWord).take
            (oddCount S.leftContext)) =
      S.leftContext.length + 1 at hRun
  rw [S.rankLower_leadingEvenCount_eq_zero hLowerFP, zero_add] at hRun
  unfold Collatz2.Word.prefixTwoDepth rankLowerExponentWord rankCut
  unfold AdjacentFerrersSwap.position
  exact hRun

end AdjacentFerrersSwap

namespace FerrersStep

/-- endpoint lower first-passage を edge lower word へ移す。 -/
theorem edge_lower_firstPassage
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    IsFirstPassageWord S.edge.lowerWord := by
  exact
    Eq.mp
      (congrArg IsFirstPassageWord S.lower_eq)
      hLowerFP

/-- selected cut で chord rank は exact に common odd total だけ増える。 -/
theorem chordRank_upper_eq_lower_add_oddTotal_at_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    Collatz2.Word.chordRank
        S.edge.rankUpperExponentWord S.edge.rankCut =
      Collatz2.Word.chordRank
          S.edge.rankLowerExponentWord S.edge.rankCut +
        S.edge.oddTotal := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hLowerF :=
    S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  have hCutPos := S.rankCell_cut_pos hLowerFP
  have hCutLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps S.edge.rankLowerExponentWord := by
    rw [S.edge.rankLowerExponentWord_oddSteps]
    unfold AdjacentFerrersSwap.rankCut AdjacentFerrersSwap.oddTotal
    omega
  have hSlope := hLowerF.prefixSlope_cross hCutPos hCutLt
  unfold Collatz2.Word.chordRank
  rw [S.edge.rankLowerExponentWord_twoSteps hEdgeLowerFP] at hSlope
  rw [S.edge.rankLowerExponentWord_oddSteps] at hSlope
  rw [S.edge.prefixTwoDepth_rankCut_eq_position_add_one hEdgeLowerFP] at hSlope
  rw [S.edge.rankUpperExponentWord_twoSteps hEdgeUpperFP]
  rw [S.edge.rankUpperExponentWord_oddSteps]
  rw [S.edge.prefixTwoDepth_rankCut_eq_position hEdgeUpperFP]
  rw [S.edge.rankLowerExponentWord_twoSteps hEdgeLowerFP]
  rw [S.edge.rankLowerExponentWord_oddSteps]
  rw [S.edge.prefixTwoDepth_rankCut_eq_position_add_one hEdgeLowerFP]
  have hLeLower :
      S.edge.oddTotal * (S.edge.position + 1) ≤
        S.edge.length * S.edge.rankCut :=
    Nat.le_of_lt hSlope
  have hPosLe :
      S.edge.position ≤ S.edge.position + 1 := by
    omega
  have hLeUpper :
      S.edge.oddTotal * S.edge.position ≤
        S.edge.length * S.edge.rankCut := by
    calc
      S.edge.oddTotal * S.edge.position
          ≤ S.edge.oddTotal * (S.edge.position + 1) :=
        Nat.mul_le_mul_left S.edge.oddTotal hPosLe
      _ ≤ S.edge.length * S.edge.rankCut := hLeLower
  have hCancelLower :
      (S.edge.length * S.edge.rankCut -
          S.edge.oddTotal * (S.edge.position + 1)) +
        S.edge.oddTotal * (S.edge.position + 1) =
      S.edge.length * S.edge.rankCut :=
    Nat.sub_add_cancel hLeLower
  have hCancelUpper :
      (S.edge.length * S.edge.rankCut -
          S.edge.oddTotal * S.edge.position) +
        S.edge.oddTotal * S.edge.position =
      S.edge.length * S.edge.rankCut :=
    Nat.sub_add_cancel hLeUpper
  have hMulSucc :
      S.edge.oddTotal * (S.edge.position + 1) =
        S.edge.oddTotal * S.edge.position + S.edge.oddTotal := by
    ring
  rw [hMulSucc] at hCancelLower
  omega

/-- selected cut の rank residue は swap で変わらない。 -/
theorem rankResidue_upper_eq_lower_at_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    Collatz2.Word.rankResidue
        S.edge.rankUpperExponentWord S.edge.rankCut =
      Collatz2.Word.rankResidue
        S.edge.rankLowerExponentWord S.edge.rankCut := by
  have hChord :=
    S.chordRank_upper_eq_lower_add_oddTotal_at_rankCut hLowerFP
  unfold Collatz2.Word.rankResidue
  rw [S.edge.rankUpperExponentWord_oddSteps]
  rw [S.edge.rankLowerExponentWord_oddSteps]
  rw [hChord]
  exact Nat.add_mod_right _ _

/-- selected cut の rank quotient は exact に1増える。 -/
theorem rankQuotient_upper_eq_lower_add_one_at_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    Collatz2.Word.rankQuotient
        S.edge.rankUpperExponentWord S.edge.rankCut =
      Collatz2.Word.rankQuotient
          S.edge.rankLowerExponentWord S.edge.rankCut + 1 := by
  have hChord :=
    S.chordRank_upper_eq_lower_add_oddTotal_at_rankCut hLowerFP
  have hP : 0 < S.edge.oddTotal := by
    have hCutPos := S.rankCell_cut_pos hLowerFP
    have hCutLt := S.edge.rankCut_lt_oddSteps
    rw [S.edge.rankUpperExponentWord_oddSteps] at hCutLt
    omega
  unfold Collatz2.Word.rankQuotient
  rw [S.edge.rankUpperExponentWord_oddSteps]
  rw [S.edge.rankLowerExponentWord_oddSteps]
  rw [hChord]
  exact Nat.add_div_right
    (Collatz2.Word.chordRank
      S.edge.rankLowerExponentWord S.edge.rankCut) hP

/--
rank checkpoint depth が不変な cut では quotient も不変。
Step 4 で non-cell cuts の encoder checkpoint invariance と結合するための transport lemma。
-/
theorem rankQuotient_eq_of_prefixTwoDepth_eq
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hDepth :
      Collatz2.Word.prefixTwoDepth S.edge.rankUpperExponentWord k =
        Collatz2.Word.prefixTwoDepth S.edge.rankLowerExponentWord k) :
    Collatz2.Word.rankQuotient S.edge.rankUpperExponentWord k =
      Collatz2.Word.rankQuotient S.edge.rankLowerExponentWord k := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  unfold Collatz2.Word.rankQuotient Collatz2.Word.chordRank
  rw [S.edge.rankUpperExponentWord_twoSteps hEdgeUpperFP]
  rw [S.edge.rankLowerExponentWord_twoSteps hEdgeLowerFP]
  rw [S.edge.rankUpperExponentWord_oddSteps]
  rw [S.edge.rankLowerExponentWord_oddSteps]
  rw [hDepth]

/-- standard Ferrers prefix-height は swap column 以外では exact に不変。 -/
theorem prefixOddCount_upper_eq_lower_of_ne_rankCellPosition
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    {i : ℕ}
    (hi : i ≠ S.edge.position) :
    prefixOddCount upper (i + 1) = prefixOddCount lower (i + 1) := by
  have h :=
    S.edge.prefixOddCount_upper_eq_lower_of_ne_position hi
  have hUpper :
      prefixOddCount upper (i + 1) =
        prefixOddCount S.edge.upperWord (i + 1) :=
    congrArg
      (fun v : ParityWord => prefixOddCount v (i + 1))
      S.upper_eq
  have hLower :
      prefixOddCount lower (i + 1) =
        prefixOddCount S.edge.lowerWord (i + 1) :=
    congrArg
      (fun v : ParityWord => prefixOddCount v (i + 1))
      S.lower_eq
  calc
    prefixOddCount upper (i + 1)
        = prefixOddCount S.edge.upperWord (i + 1) := hUpper
    _ = prefixOddCount S.edge.lowerWord (i + 1) := h
    _ = prefixOddCount lower (i + 1) := hLower.symm

end FerrersStep

end CSTMicro
end Collatz2
