import CollatzLean.Collatz2.CSTMicro.CarryGeometry.UniversalRankTopFerrersStep
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.PositiveCostFerrersPotential

set_option linter.style.longLine false

/-!
# Actual Ferrers-step rank-top ledger

前ファイルの selected / non-selected transport を ordinary representative の総和へ足し上げる。
一 step の cell cost を `C > 0`、common terminal gap を `G` とすると

  topUpper - topLower = -3*C + G*lambda(G,C)

が exact に成り立つ。

さらに normalized cocycle

  qUpper - qLower = G*carryIndicator - C

と結合し、actual rank-top numerator

  Jnum(v) = topSum(v) - 3*q(v)

について

  Jnum(upper) = Jnum(lower) + G*(lambda - 3*carryIndicator)

を得る。primitive 条件は一切使わない。
-/

namespace Collatz2
namespace CSTMicro

namespace AdjacentFerrersSwap

/-- lower encoded terminal gap は standard lower terminal gap と一致。 -/
theorem rankLower_terminalGap_eq_wordTerminalGap
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.terminalGap S.rankLowerExponentWord =
      wordTerminalGap S.lowerWord := by
  unfold Collatz2.Word.terminalGap wordTerminalGap
  rw [S.rankLowerExponentWord_twoSteps hLowerFP]
  rw [S.rankLowerExponentWord_oddSteps]
  rw [S.lowerWord_length, S.lowerWord_oddCount]

/-- upper encoded terminal gap も standard lower terminal gap と一致。 -/
theorem rankUpper_terminalGap_eq_lowerWordTerminalGap
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.terminalGap S.rankUpperExponentWord =
      wordTerminalGap S.lowerWord := by
  calc
    Collatz2.Word.terminalGap S.rankUpperExponentWord
        = Collatz2.Word.terminalGap S.rankLowerExponentWord :=
          (S.rankLower_terminalGap_eq_rankUpper_terminalGap
            hLowerFP hUpperFP).symm
    _ = wordTerminalGap S.lowerWord :=
          S.rankLower_terminalGap_eq_wordTerminalGap hLowerFP

end AdjacentFerrersSwap

namespace FerrersStep

/-- edge lower / upper odd-only top sum の integer lift。 -/
noncomputable def rankTopLowerSumInt
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) : ℤ :=
  let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  let hF := S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  (Collatz2.Word.rankTopSum hF : ℕ)

noncomputable def rankTopUpperSumInt
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) : ℤ :=
  let hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  let hF := S.edge.rankUpperExponentWord_firstCrossing hUpperFP
  (Collatz2.Word.rankTopSum hF : ℕ)

/-- one-step rank-top lambda。 -/
noncomputable def actualRankTopLambda
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ :=
  rankTopLambda
    (wordTerminalGap S.edge.lowerWord)
    S.edge.fareyCellCost.toNat

/-- positive-residue cell では actual lambda は finite alphabet `{0,1,2,3}`。 -/
theorem actualRankTopLambda_cases_of_residue_pos
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hResiduePos : 0 < S.edge.toFareyCellPacket.residue) :
    S.actualRankTopLambda = 0 ∨
      S.actualRankTopLambda = 1 ∨
      S.actualRankTopLambda = 2 ∨
      S.actualRankTopLambda = 3 := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have h := S.rankTopLambda_cell_cases hLowerFP hResiduePos
  simpa [actualRankTopLambda, ← S.lower_eq] using h

/--
rank-top ordinary sum の one-step exact jump。

selected term 以外は全て cancel し、selected term の差だけが残る。
-/
theorem rankTopUpperSumInt_eq_lower_sub_threeCost_add_gap_lambda
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.rankTopUpperSumInt hLowerFP =
      S.rankTopLowerSumInt hLowerFP -
        3 * S.edge.fareyCellCost.toNat +
        (wordTerminalGap S.edge.lowerWord : ℤ) *
          (S.actualRankTopLambda : ℤ) := by
  let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  let hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  let hLowerF := S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  let hUpperF := S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
  let p := S.edge.oddTotal
  let t := S.edge.rankCut
  let G := wordTerminalGap S.edge.lowerWord
  let C := S.edge.fareyCellCost.toNat
  have hCutMem : t ∈ Finset.range p := by
    apply Finset.mem_range.mpr
    have h := S.edge.rankCut_lt_oddSteps
    rw [S.edge.rankUpperExponentWord_oddSteps] at h
    simpa [p, t] using h
  have hUpperCast :
      ((Collatz2.Word.rankTopSum hUpperF : ℕ) : ℤ) =
        Finset.sum (Finset.range p)
          (fun k => (Collatz2.Word.rankTopRepresentative hUpperF k : ℤ)) := by
    unfold Collatz2.Word.rankTopSum
    rw [S.edge.rankUpperExponentWord_oddSteps]
    dsimp [p]
    norm_cast
  have hLowerCast :
      ((Collatz2.Word.rankTopSum hLowerF : ℕ) : ℤ) =
        Finset.sum (Finset.range p)
          (fun k => (Collatz2.Word.rankTopRepresentative hLowerF k : ℤ)) := by
    unfold Collatz2.Word.rankTopSum
    rw [S.edge.rankLowerExponentWord_oddSteps]
    dsimp [p]
    norm_cast
  have hSingle :
      Finset.sum (Finset.range p)
          (fun k =>
            (Collatz2.Word.rankTopRepresentative hUpperF k : ℤ) -
              (Collatz2.Word.rankTopRepresentative hLowerF k : ℤ)) =
        (Collatz2.Word.rankTopRepresentative hUpperF t : ℤ) -
          (Collatz2.Word.rankTopRepresentative hLowerF t : ℤ) := by
    apply Finset.sum_eq_single t
    · intro b hb hbt
      have hbNe : b ≠ S.edge.rankCut := by
        simpa [t] using hbt
      have hSame :=
        S.rankTopRepresentative_upper_eq_lower_of_ne_rankCut
          hLowerFP hbNe
      have hSame' :
          Collatz2.Word.rankTopRepresentative hUpperF b =
            Collatz2.Word.rankTopRepresentative hLowerF b := by
        simpa [hUpperF, hLowerF, hEdgeUpperFP, hEdgeLowerFP] using hSame
      rw [hSame']
      ring
    · intro htNot
      exact False.elim (htNot hCutMem)
  have hSumDiff :
      ((Collatz2.Word.rankTopSum hUpperF : ℕ) : ℤ) -
          ((Collatz2.Word.rankTopSum hLowerF : ℕ) : ℤ) =
        (Collatz2.Word.rankTopRepresentative hUpperF t : ℤ) -
          (Collatz2.Word.rankTopRepresentative hLowerF t : ℤ) := by
    rw [hUpperCast, hLowerCast]
    rw [← Finset.sum_sub_distrib]
    exact hSingle
  have hSelUraw :=
    S.selected_rankTopRepresentative_upper_eq_residue3 hLowerFP
  have hSelLraw :=
    S.selected_rankTopRepresentative_lower_eq_residue6 hLowerFP
  have hGapU :=
    S.edge.rankUpper_terminalGap_eq_lowerWordTerminalGap
      hEdgeLowerFP hEdgeUpperFP
  have hGapL :=
    S.edge.rankLower_terminalGap_eq_wordTerminalGap hEdgeLowerFP
  have hSelU0 :
      Collatz2.Word.rankTopRepresentative hUpperF t =
        rankTopResidue3
          (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)
          C := by
    simpa [hUpperF, hEdgeUpperFP, t, C] using hSelUraw
  have hSelL0 :
      Collatz2.Word.rankTopRepresentative hLowerF t =
        rankTopResidue6
          (Collatz2.Word.terminalGap S.edge.rankLowerExponentWord)
          C := by
    simpa [hLowerF, hEdgeLowerFP, t, C] using hSelLraw
  have hResidue3Gap :
      rankTopResidue3
          (Collatz2.Word.terminalGap S.edge.rankUpperExponentWord)
          C =
        rankTopResidue3 G C := by
    apply congrArg (fun X : ℕ => rankTopResidue3 X C)
    simpa [G] using hGapU
  have hResidue6Gap :
      rankTopResidue6
          (Collatz2.Word.terminalGap S.edge.rankLowerExponentWord)
          C =
        rankTopResidue6 G C := by
    apply congrArg (fun X : ℕ => rankTopResidue6 X C)
    simpa [G] using hGapL
  have hSelU :
      Collatz2.Word.rankTopRepresentative hUpperF t =
        rankTopResidue3 G C :=
    hSelU0.trans hResidue3Gap
  have hSelL :
      Collatz2.Word.rankTopRepresentative hLowerF t =
        rankTopResidue6 G C :=
    hSelL0.trans hResidue6Gap
  have hLocal := rankTopResidue3_sub_rankTopResidue6 (G := G) (C := C)
  have hDiff :
      ((Collatz2.Word.rankTopSum hUpperF : ℕ) : ℤ) -
          ((Collatz2.Word.rankTopSum hLowerF : ℕ) : ℤ) =
        -(3 * (C : ℤ)) + (G : ℤ) * (rankTopLambda G C : ℤ) := by
    rw [hSumDiff, hSelU, hSelL]
    exact hLocal
  unfold rankTopUpperSumInt rankTopLowerSumInt actualRankTopLambda
  dsimp [hUpperF, hLowerF, hEdgeUpperFP, hEdgeLowerFP, G, C] at hDiff ⊢
  linarith [hDiff]

/-- endpoint parity word から直接読む universal rank-top sum。 -/
noncomputable def parityRankTopSum
    (v : ParityWord)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) : ℕ :=
  Collatz2.Word.rankTopSum (hFP.exponentWordOfParity_firstCrossing hLen)

/-- proof 引数の違いは rank-top sum の値に影響しない。 -/
theorem parityRankTopSum_proof_irrel
    (v : ParityWord)
    (hFP₁ hFP₂ : IsFirstPassageWord v)
    (hLen₁ hLen₂ : 1 < v.length) :
    parityRankTopSum v hFP₁ hLen₁ = parityRankTopSum v hFP₂ hLen₂ := by
  have h1 : hFP₁ = hFP₂ := Subsingleton.elim _ _
  have h2 : hLen₁ = hLen₂ := Subsingleton.elim _ _
  subst hFP₂
  subst hLen₂
  rfl

/-- endpoint normalized coordinate を引いた rank-top numerator。 -/
noncomputable def parityRankTopNumerator
    (v : ParityWord)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) : ℤ :=
  (parityRankTopSum v hFP hLen : ℤ) -
    3 * normalizedSeparationDefectInt v

/-- endpoint proof 引数の違いは numerator にも影響しない。 -/
theorem parityRankTopNumerator_proof_irrel
    (v : ParityWord)
    (hFP₁ hFP₂ : IsFirstPassageWord v)
    (hLen₁ hLen₂ : 1 < v.length) :
    parityRankTopNumerator v hFP₁ hLen₁ =
      parityRankTopNumerator v hFP₂ hLen₂ := by
  unfold parityRankTopNumerator
  rw [parityRankTopSum_proof_irrel v hFP₁ hFP₂ hLen₁ hLen₂]

/-- underlying word が等しければ rankTopSum は
    FirstCrossing proof の取り方によらず一致する。 -/
theorem rankTopSum_eq_of_word_eq
    {w₁ w₂ : Collatz2.Word}
    (h : w₁ = w₂)
    (h₁ : w₁.FirstCrossing)
    (h₂ : w₂.FirstCrossing) :
    Collatz2.Word.rankTopSum h₁ =
      Collatz2.Word.rankTopSum h₂ := by
  subst w₂
  have hp : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- lower endpoint から直接読んだ rank-top sum は、
    FerrersStep の既存 lower rank-top sum と一致する。 -/
theorem parityRankTopSum_eq_rankTopLowerSumInt
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hLowerLen : 1 < lower.length) :
    (parityRankTopSum lower hLowerFP hLowerLen : ℤ) =
      S.rankTopLowerSumInt hLowerFP := by
  have hDirect :
      (exponentWordOfParity lower).FirstCrossing :=
    hLowerFP.exponentWordOfParity_firstCrossing hLowerLen
  have hEdgeLowerFP :
      IsFirstPassageWord S.edge.lowerWord :=
    S.edge_lower_firstPassage hLowerFP
  have hRank :
      S.edge.rankLowerExponentWord.FirstCrossing :=
    S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  have hWord :
      exponentWordOfParity lower =
        S.edge.rankLowerExponentWord := by
    change
      exponentWordOfParity lower =
        exponentWordOfParity S.edge.lowerWord
    exact congrArg exponentWordOfParity S.lower_eq
  have hNat :
      Collatz2.Word.rankTopSum hDirect =
        Collatz2.Word.rankTopSum hRank :=
    rankTopSum_eq_of_word_eq hWord hDirect hRank
  simpa only [
    parityRankTopSum,
    rankTopLowerSumInt
  ] using congrArg (fun n : ℕ => (n : ℤ)) hNat


/-- upper endpoint から直接読んだ rank-top sum は、
    FerrersStep の既存 upper rank-top sum と一致する。 -/
theorem parityRankTopSum_eq_rankTopUpperSumInt
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hLowerLen : 1 < lower.length) :
    let hUpperFP : IsFirstPassageWord upper :=
      Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
        (S.edge_upper_firstPassage_of_lower hLowerFP)
    let hUpperLen : 1 < upper.length := by
      rw [← S.length_eq]
      exact hLowerLen
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      S.rankTopUpperSumInt hLowerFP := by
  let hEdgeUpperFP : IsFirstPassageWord S.edge.upperWord :=
    S.edge_upper_firstPassage_of_lower hLowerFP
  let hUpperFP : IsFirstPassageWord upper :=
    Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
      hEdgeUpperFP
  let hUpperLen : 1 < upper.length := by
    rw [← S.length_eq]
    exact hLowerLen
  change
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      S.rankTopUpperSumInt hLowerFP
  have hDirect :
      (exponentWordOfParity upper).FirstCrossing :=
    hUpperFP.exponentWordOfParity_firstCrossing hUpperLen
  have hRank :
      S.edge.rankUpperExponentWord.FirstCrossing :=
    S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
  have hWord :
      exponentWordOfParity upper =
        S.edge.rankUpperExponentWord := by
    change
      exponentWordOfParity upper =
        exponentWordOfParity S.edge.upperWord
    exact congrArg exponentWordOfParity S.upper_eq
  have hNat :
      Collatz2.Word.rankTopSum hDirect =
        Collatz2.Word.rankTopSum hRank :=
    rankTopSum_eq_of_word_eq hWord hDirect hRank
  simpa only [
    parityRankTopSum,
    rankTopUpperSumInt
  ] using congrArg (fun n : ℕ => (n : ℤ)) hNat


/-- one step の endpoint rank-top sum jump。 -/
theorem parityRankTopSum_step
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hLowerLen : 1 < lower.length) :
    let hUpperFP : IsFirstPassageWord upper :=
      Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
        (S.edge_upper_firstPassage_of_lower hLowerFP)
    let hUpperLen : 1 < upper.length := by
      rw [← S.length_eq]
      exact hLowerLen
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      (parityRankTopSum lower hLowerFP hLowerLen : ℤ) -
        3 * S.edge.fareyCellCost.toNat +
        (wordTerminalGap lower : ℤ) *
          (S.actualRankTopLambda : ℤ) := by
  let hUpperFP : IsFirstPassageWord upper :=
    Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
      (S.edge_upper_firstPassage_of_lower hLowerFP)
  let hUpperLen : 1 < upper.length := by
    rw [← S.length_eq]
    exact hLowerLen
  change
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      (parityRankTopSum lower hLowerFP hLowerLen : ℤ) -
        3 * S.edge.fareyCellCost.toNat +
        (wordTerminalGap lower : ℤ) *
          (S.actualRankTopLambda : ℤ)
  have hUpper :
      (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
        S.rankTopUpperSumInt hLowerFP := by
    exact parityRankTopSum_eq_rankTopUpperSumInt
      S hLowerFP hLowerLen
  have hLower :
      (parityRankTopSum lower hLowerFP hLowerLen : ℤ) =
        S.rankTopLowerSumInt hLowerFP := by
    exact parityRankTopSum_eq_rankTopLowerSumInt
      S hLowerFP hLowerLen
  rw [hUpper, hLower]
  have hEdge :=
    S.rankTopUpperSumInt_eq_lower_sub_threeCost_add_gap_lambda
      hLowerFP
  have hGap :
      wordTerminalGap S.edge.lowerWord =
        wordTerminalGap lower :=
    congrArg wordTerminalGap S.lower_eq.symm
  rw [hGap] at hEdge
  exact hEdge

/--
実際の normalized q を含む one-step numerator law。

  ΔJnum = G * (lambda - 3*carryIndicator).
-/
theorem parityRankTopNumerator_step
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hLowerLen : 1 < lower.length) :
    let hUpperFP : IsFirstPassageWord upper :=
      Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
        (S.edge_upper_firstPassage_of_lower hLowerFP)
    let hUpperLen : 1 < upper.length := by
      rw [← S.length_eq]
      exact hLowerLen
    parityRankTopNumerator upper hUpperFP hUpperLen =
      parityRankTopNumerator lower hLowerFP hLowerLen +
        (wordTerminalGap lower : ℤ) *
          ((S.actualRankTopLambda : ℤ) -
            3 * (S.normalizedCarryIndicator : ℤ)) := by
  let hUpperFP : IsFirstPassageWord upper :=
    Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
      (S.edge_upper_firstPassage_of_lower hLowerFP)
  let hUpperLen : 1 < upper.length := by
    rw [← S.length_eq]
    exact hLowerLen
  have hTop := S.parityRankTopSum_step hLowerFP hLowerLen
  have hDelta :=
    S.normalizedStepDelta_eq_gap_mul_carryIndicator_sub_cellCost hLowerFP
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hGEdge :=
    S.edge.fareyPacket_G_eq_wordTerminalGap hEdgeLowerFP.2.2
  have hG :
      S.edge.toFareyCellPacket.G = (wordTerminalGap lower : ℤ) := by
    calc
      S.edge.toFareyCellPacket.G
          = (wordTerminalGap S.edge.lowerWord : ℤ) := hGEdge
      _ = (wordTerminalGap lower : ℤ) := by
          exact_mod_cast (congrArg wordTerminalGap S.lower_eq.symm)
  have hCost := S.fareyCellCost_toNat_cast hLowerFP
  have hQ :
      normalizedSeparationDefectInt upper =
        normalizedSeparationDefectInt lower +
          (wordTerminalGap lower : ℤ) *
            (S.normalizedCarryIndicator : ℤ) -
          (S.edge.fareyCellCost.toNat : ℤ) := by
    unfold normalizedStepDelta at hDelta
    rw [hG, ← hCost] at hDelta
    linarith
  unfold parityRankTopNumerator
  dsimp [hUpperFP, hUpperLen] at hTop ⊢
  rw [hTop, hQ]
  ring

end FerrersStep

end CSTMicro
end Collatz2
