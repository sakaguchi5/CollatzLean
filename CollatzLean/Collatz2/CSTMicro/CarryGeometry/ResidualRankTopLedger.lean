import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RankTopChainWindingLedger

/-!
# Residual rank-top ledger

任意の positive first-passage cell cost `C` を common terminal gap `G` で

  C = G * a + r,   0 <= r < G

と Euclidean decomposition する。

rank-top quotient jump

  lambda(G,C) = floor(6C/G) - floor(3C/G)

は

  lambda(G,C) = 3*a + lambda(G,r)

へ exact に分解でき、remainder side は常に

  lambda(G,r) in {0,1,2,3}

となる。従って cell residue の符号を仮定せずに、unbounded part を
`3*a` へ吸収し、bounded four-letter remainder だけを残せる。
-/

namespace Collatz2
namespace CSTMicro

/-- cell cost の full-gap quotient。 -/
def rankTopCostQuotient (G C : ℕ) : ℕ := C / G

/-- cell cost の bounded residual part。 -/
def rankTopResidualCost (G C : ℕ) : ℕ := C % G

/-- bounded residual cost に対する four-letter lambda。 -/
def residualRankTopLambda (G C : ℕ) : ℕ :=
  rankTopLambda G (rankTopResidualCost G C)

/-- Euclidean decomposition `C = G*a+r`。 -/
theorem rankTopCost_eq_gap_mul_quotient_add_residual
    (G C : ℕ) :
    C = G * rankTopCostQuotient G C + rankTopResidualCost G C := by
  unfold rankTopCostQuotient rankTopResidualCost
  have h := Nat.mod_add_div C G
  omega

/-- positive modulus では residual cost は strict bounded。 -/
theorem rankTopResidualCost_lt_gap
    {G C : ℕ}
    (hG : 0 < G) :
    rankTopResidualCost G C < G := by
  unfold rankTopResidualCost
  exact Nat.mod_lt _ hG

/-- `3C/G` の quotient decomposition。 -/
theorem three_mul_cost_div_eq_three_mul_quotient_add_residual_div
    {G C : ℕ}
    (hG : 0 < G) :
    (3 * C) / G =
      3 * rankTopCostQuotient G C +
        (3 * rankTopResidualCost G C) / G := by
  let a := rankTopCostQuotient G C
  let r := rankTopResidualCost G C
  have hC : C = G * a + r := by
    simpa [a, r, Nat.add_comm] using
      rankTopCost_eq_gap_mul_quotient_add_residual G C
  have hForm : 3 * C = 3 * r + G * (3 * a) := by
    rw [hC]
    ring
  rw [hForm]
  have hDiv := Nat.add_mul_div_left (3 * r) (3 * a) hG
  simpa [a, r, Nat.add_comm] using hDiv

/-- `6C/G` の quotient decomposition。 -/
theorem six_mul_cost_div_eq_six_mul_quotient_add_residual_div
    {G C : ℕ}
    (hG : 0 < G) :
    (6 * C) / G =
      6 * rankTopCostQuotient G C +
        (6 * rankTopResidualCost G C) / G := by
  let a := rankTopCostQuotient G C
  let r := rankTopResidualCost G C
  have hC : C = G * a + r := by
    simpa [a, r, Nat.add_comm] using
      rankTopCost_eq_gap_mul_quotient_add_residual G C
  have hForm : 6 * C = 6 * r + G * (6 * a) := by
    rw [hC]
    ring
  rw [hForm]
  have hDiv := Nat.add_mul_div_left (6 * r) (6 * a) hG
  simpa [a, r, Nat.add_comm] using hDiv

/--
full lambda は unbounded quotient `3*a` と bounded remainder lambda に分かれる。
-/
theorem rankTopLambda_eq_three_mul_quotient_add_residualLambda
    {G C : ℕ}
    (hG : 0 < G) :
    rankTopLambda G C =
      3 * rankTopCostQuotient G C + residualRankTopLambda G C := by
  let a := rankTopCostQuotient G C
  let r := rankTopResidualCost G C
  have h3 :=
    three_mul_cost_div_eq_three_mul_quotient_add_residual_div
      (G := G) (C := C) hG
  have h6 :=
    six_mul_cost_div_eq_six_mul_quotient_add_residual_div
      (G := G) (C := C) hG
  have hLe : (3 * r) / G ≤ (6 * r) / G :=
    three_mul_div_le_six_mul_div
  simp only [
    rankTopLambda,
    residualRankTopLambda,
    rankTopCostQuotient,
    rankTopResidualCost
  ] at h3 h6 ⊢
  dsimp [a, r] at hLe
  rw [h6, h3]
  have hSix :
      6 * (C / G) =
        3 * (C / G) + 3 * (C / G) := by
    omega
  rw [hSix]
  rw [Nat.add_assoc]
  rw [Nat.add_sub_add_left]
  have hLe' :
      3 * (C % G) / G ≤ 6 * (C % G) / G := by
    simpa [rankTopResidualCost] using hLe
  exact Nat.add_sub_assoc hLe' (3 * (C / G))

/-- residual lambda は cell residue の符号に関係なく four-letter alphabet。 -/
theorem residualRankTopLambda_cases
    {G C : ℕ}
    (hG : 0 < G) :
    residualRankTopLambda G C = 0 ∨
      residualRankTopLambda G C = 1 ∨
      residualRankTopLambda G C = 2 ∨
      residualRankTopLambda G C = 3 := by
  have hR : rankTopResidualCost G C < G :=
    rankTopResidualCost_lt_gap hG
  unfold residualRankTopLambda
  exact rankTopLambda_cases hG hR

namespace FerrersStep

/-- actual first-passage cell の common gap。 -/
def actualRankTopGap
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ :=
  wordTerminalGap S.edge.lowerWord

/-- actual cell cost の full-gap quotient。 -/
def actualRankTopCostQuotient
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ :=
  rankTopCostQuotient S.actualRankTopGap S.edge.fareyCellCost.toNat

/-- actual cell cost の bounded residual。 -/
def actualRankTopResidualCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ :=
  rankTopResidualCost S.actualRankTopGap S.edge.fareyCellCost.toNat

/-- actual residual four-letter lambda。 -/
def actualResidualRankTopLambda
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ :=
  residualRankTopLambda S.actualRankTopGap S.edge.fareyCellCost.toNat

/-- carry winding から full-gap cost quotient を引いた effective winding。 -/
noncomputable def actualEffectiveWinding
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℤ :=
  (S.normalizedCarryIndicator : ℤ) -
    (S.actualRankTopCostQuotient : ℤ)

/-- first-passage cell の common gap は positive。 -/
theorem actualRankTopGap_pos
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < S.actualRankTopGap := by
  have hEdgeFP := S.edge_lower_firstPassage hLowerFP
  have hContract := hEdgeFP.2.2
  unfold actualRankTopGap wordTerminalGap
  unfold CoefficientContracting at hContract
  exact Nat.sub_pos_of_lt hContract

/-- actual lambda も quotient + residual four-letter lambda に exact 分解。 -/
theorem actualRankTopLambda_eq_three_mul_costQuotient_add_residualLambda
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.actualRankTopLambda =
      3 * S.actualRankTopCostQuotient +
        S.actualResidualRankTopLambda := by
  have hG := S.actualRankTopGap_pos hLowerFP
  unfold actualRankTopLambda actualRankTopCostQuotient
    actualResidualRankTopLambda actualRankTopGap
  exact rankTopLambda_eq_three_mul_quotient_add_residualLambda hG

/-- residualized actual lambda は全 first-passage step で無条件に four-letter。 -/
theorem actualResidualRankTopLambda_cases
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.actualResidualRankTopLambda = 0 ∨
      S.actualResidualRankTopLambda = 1 ∨
      S.actualResidualRankTopLambda = 2 ∨
      S.actualResidualRankTopLambda = 3 := by
  exact residualRankTopLambda_cases (S.actualRankTopGap_pos hLowerFP)

/-- actual positive cost の natural cast。 -/
theorem fareyCellCost_eq_toNat_int
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.fareyCellCost = (S.edge.fareyCellCost.toNat : ℤ) := by
  exact (S.fareyCellCost_toNat_cast hLowerFP).symm

/--
normalized local cocycle の residualized form。

Delta q = G * effectiveWinding - residualCost.
-/
theorem normalizedStepDelta_eq_gap_mul_effectiveWinding_sub_residualCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    normalizedStepDelta lower upper =
      (S.actualRankTopGap : ℤ) * S.actualEffectiveWinding -
        (S.actualRankTopResidualCost : ℤ) := by
  have hOld :=
    S.normalizedStepDelta_eq_gap_mul_carryIndicator_sub_cellCost hLowerFP
  have hEdgeFP := S.edge_lower_firstPassage hLowerFP
  have hGap :=
    S.edge.fareyPacket_G_eq_wordTerminalGap hEdgeFP.2.2
  have hCost :=
    S.fareyCellCost_eq_toNat_int hLowerFP
  have hDecomp :=
    rankTopCost_eq_gap_mul_quotient_add_residual
      S.actualRankTopGap S.edge.fareyCellCost.toNat
  have hDecompZ :
      (S.edge.fareyCellCost.toNat : ℤ) =
        (S.actualRankTopGap : ℤ) *
          (rankTopCostQuotient
            S.actualRankTopGap
            S.edge.fareyCellCost.toNat : ℤ) +
        (rankTopResidualCost
          S.actualRankTopGap
          S.edge.fareyCellCost.toNat : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ℤ)) hDecomp
  rw [hGap, hCost] at hOld
  unfold actualEffectiveWinding
    actualRankTopCostQuotient
    actualRankTopResidualCost
  dsimp [actualRankTopGap] at hDecompZ ⊢
  rw [hOld]
  rw [hDecompZ]
  ring

/--
actual rank-top numerator step も residual four-letter system へ落ちる。

  Delta Jnum = G * (residualLambda - 3*effectiveWinding).
-/
theorem parityRankTopNumerator_step_residualized
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
          ((S.actualResidualRankTopLambda : ℤ) -
            3 * S.actualEffectiveWinding) := by
  let hUpperFP : IsFirstPassageWord upper :=
    Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
      (S.edge_upper_firstPassage_of_lower hLowerFP)
  let hUpperLen : 1 < upper.length := by
    rw [← S.length_eq]
    exact hLowerLen
  have hOld := S.parityRankTopNumerator_step hLowerFP hLowerLen
  have hLam :=
    S.actualRankTopLambda_eq_three_mul_costQuotient_add_residualLambda
      hLowerFP
  unfold actualEffectiveWinding at *
  dsimp [hUpperFP, hUpperLen] at hOld ⊢
  rw [hLam] at hOld
  push_cast at hOld
  ring_nf at hOld ⊢
  exact hOld

end FerrersStep

end CSTMicro
end Collatz2
