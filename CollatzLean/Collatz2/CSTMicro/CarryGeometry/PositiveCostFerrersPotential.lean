import CollatzLean.Collatz2.CSTMicro.CarryGeometry.BoundaryRespectingCellSlack
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersCellResiduePotential


/-!
# Positive Ferrers cell-cost potential and carry winding

`MinimalBadCellCostObstruction` で得た

  cellCost = G - D

を Ferrers diagram 全体へ積分する。

signed terminal gap

  Gz(v) = 2^|v| - 3^odd(v)

と residue potential `Phi(v)` に対して

  Psi(v) = Gz(v) * ferrersInversion(v) - Phi(v)

と置くと、一つの `01 -> 10` Ferrers step で

  Psi(upper) = Psi(lower) + cellCost.

first-passage chain では terminal coefficient が contracting なので各 cell cost は
strict positive。さらに carry indicator を導入すると exact に

  q_finish
    = q_start + G * carryCount - totalCellCost

となる。actual critical boundary から minimal bad B まででは

  G * carryCount >= FerrersDistance + 1

が従う。
-/

namespace Collatz2
namespace CSTMicro

/-- subtraction truncationを使わない signed terminal gap。 -/
def ferrersSignedTerminalGap (v : ParityWord) : ℤ :=
  (2 : ℤ) ^ v.length - (3 : ℤ) ^ oddCount v

/-- positive cell cost を積分する global Ferrers potential。 -/
def ferrersCellCostPotential (v : ParityWord) : ℤ :=
  ferrersSignedTerminalGap v * (ferrersInversion v : ℤ) -
    ferrersCellResiduePotential v

/-- Ferrers endpoints 間の inversion distance。 -/
def ferrersDistance (start finish : ParityWord) : ℕ :=
  ferrersInversion finish - ferrersInversion start

namespace AdjacentFerrersSwap

/-- actual cell の Farey gap は lower word の signed terminal gap。 -/
theorem farey_G_eq_signedTerminalGap_lower
    (S : AdjacentFerrersSwap) :
    S.toFareyCellPacket.G = ferrersSignedTerminalGap S.lowerWord := by
  unfold ferrersSignedTerminalGap
  rw [S.lowerWord_length, S.lowerWord_oddCount]
  rfl

/-- actual cell の Farey gap は upper word の signed terminal gap。 -/
theorem farey_G_eq_signedTerminalGap_upper
    (S : AdjacentFerrersSwap) :
    S.toFareyCellPacket.G = ferrersSignedTerminalGap S.upperWord := by
  unfold ferrersSignedTerminalGap
  rw [S.upperWord_length, S.upperWord_oddCount]
  rfl

end AdjacentFerrersSwap

namespace FerrersStep

/-- 一 step で cost potential は exact に `G-D = cellCost` 増える。 -/
theorem ferrersCellCostPotential_upper_eq_lower_add_cellCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    ferrersCellCostPotential upper =
      ferrersCellCostPotential lower + S.edge.fareyCellCost := by
  have hInv := S.ferrersInversion_succ
  have hResid := S.ferrersCellResiduePotential_upper_eq_lower_add_residue
  have hGapLower :
      ferrersSignedTerminalGap lower = S.edge.toFareyCellPacket.G := by
    calc
      ferrersSignedTerminalGap lower
          = ferrersSignedTerminalGap S.edge.lowerWord :=
        congrArg ferrersSignedTerminalGap S.lower_eq
      _ = S.edge.toFareyCellPacket.G :=
        S.edge.farey_G_eq_signedTerminalGap_lower.symm
  have hGapUpper :
      ferrersSignedTerminalGap upper = S.edge.toFareyCellPacket.G := by
    calc
      ferrersSignedTerminalGap upper
          = ferrersSignedTerminalGap S.edge.upperWord :=
        congrArg ferrersSignedTerminalGap S.upper_eq
      _ = S.edge.toFareyCellPacket.G :=
        S.edge.farey_G_eq_signedTerminalGap_upper.symm
  unfold ferrersCellCostPotential
  rw [hGapLower, hGapUpper, hInv, hResid]
  unfold AdjacentFerrersSwap.fareyCellCost
  push_cast
  ring
/-- first-passage step では cost potential は strict に増える。 -/
theorem ferrersCellCostPotential_lt
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    ferrersCellCostPotential lower < ferrersCellCostPotential upper := by
  have hContract : 3 ^ S.edge.oddTotal < S.edge.modulus := by
    have h := hLowerFP.2.2
    unfold CoefficientContracting at h
    rw [S.lower_eq] at h
    simpa [AdjacentFerrersSwap.modulus] using h
  have hCost : 0 < S.edge.fareyCellCost :=
    S.edge.fareyCellCost_pos_of_contracting hContract
  rw [S.ferrersCellCostPotential_upper_eq_lower_add_cellCost]
  linarith

/-- carry なら1、no-carryなら0。 -/
noncomputable def normalizedCarryIndicator
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) : ℕ := by
  classical
  exact if S.edge.HasCarry then 1 else 0

/-- carry branch の indicator。 -/
theorem normalizedCarryIndicator_eq_one_of_hasCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hCarry : S.edge.HasCarry) :
    S.normalizedCarryIndicator = 1 := by
  classical
  unfold normalizedCarryIndicator
  rw [ite_eq_left hCarry]

/-- no-carry branch の indicator。 -/
theorem normalizedCarryIndicator_eq_zero_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hNoCarry : S.edge.NoCarry) :
    S.normalizedCarryIndicator = 0 := by
  have hNotCarry : ¬ S.edge.HasCarry := by
    intro hCarry
    have hNoCarry' :
        S.edge.lowerR + S.edge.deltaR < S.edge.modulus := by
      exact hNoCarry
    have hCarry' :
        S.edge.modulus ≤ S.edge.lowerR + S.edge.deltaR := by
      exact hCarry
    omega
  unfold normalizedCarryIndicator
  rw [ite_eq_right hNotCarry]

/-- 一 step では carry/no-carry indicator の和は exact に1。 -/
theorem normalizedCarryIndicator_add_noCarryIndicator_eq_one
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.normalizedCarryIndicator + S.normalizedNoCarryIndicator = 1 := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · rw [S.normalizedCarryIndicator_eq_zero_of_noCarry hNo]
    rw [S.normalizedNoCarryIndicator_eq_one_of_noCarry hNo]
  · rw [S.normalizedCarryIndicator_eq_one_of_hasCarry hCarry]
    rw [S.normalizedNoCarryIndicator_eq_zero_of_hasCarry hCarry]

/--
positive cost form の exact local cocycle。

  carry    : Delta q = G - C
  no-carry : Delta q =   - C

を一式にして

  Delta q = G * carryIndicator - C.
-/
theorem normalizedStepDelta_eq_gap_mul_carryIndicator_sub_cellCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    normalizedStepDelta lower upper =
      S.edge.toFareyCellPacket.G * (S.normalizedCarryIndicator : ℤ) -
        S.edge.fareyCellCost := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · rw [S.normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
          hLowerFP hNo]
    rw [S.normalizedCarryIndicator_eq_zero_of_noCarry hNo]
    unfold AdjacentFerrersSwap.fareyCellCost
    push_cast
    ring
  · rw [S.normalizedStepDelta_eq_fareyResidue_of_hasCarry
          hLowerFP hCarry]
    rw [S.normalizedCarryIndicator_eq_one_of_hasCarry hCarry]
    unfold AdjacentFerrersSwap.fareyCellCost
    push_cast
    ring

end FerrersStep

namespace FerrersChain

/-- chain が通過する positive cell cost の総和。 -/
noncomputable def normalizedCellCostSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℤ
  | .refl _ => 0
  | .step C S =>
      C.normalizedCellCostSum + S.edge.fareyCellCost

/-- chain 中の carry step 数。 -/
noncomputable def normalizedCarryCount
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S =>
      C.normalizedCarryCount + S.normalizedCarryIndicator

/-- chain の step 数。 -/
def ferrersStepCount
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C _ => C.ferrersStepCount + 1

/-- step 数は endpoint inversion difference そのもの。 -/
theorem ferrersStepCount_eq_ferrersDistance
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.ferrersStepCount = ferrersDistance start finish := by
  induction C with
  | refl =>
      simp [ferrersStepCount, ferrersDistance]
  | @step u v C S ih =>
      have hInv := S.ferrersInversion_succ
      have hLe := C.ferrersInversion_le
      unfold ferrersDistance at ih ⊢
      change C.ferrersStepCount + 1 =
        ferrersInversion v - ferrersInversion start
      rw [ih, hInv]
      omega

/-- carry count + no-carry count = total step count。 -/
theorem normalizedCarryCount_add_noCarryCount_eq_stepCount
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.normalizedCarryCount + C.normalizedNoCarryCount = C.ferrersStepCount := by
  induction C with
  | refl =>
      simp [normalizedCarryCount, normalizedNoCarryCount, ferrersStepCount]
  | @step u v C S ih =>
      change
        (C.normalizedCarryCount + S.normalizedCarryIndicator) +
            (C.normalizedNoCarryCount + S.normalizedNoCarryIndicator) =
          C.ferrersStepCount + 1
      have hOne := S.normalizedCarryIndicator_add_noCarryIndicator_eq_one
      omega

/-- total cell cost は global cost potential difference に telescope する。 -/
theorem normalizedCellCostSum_eq_potential_sub
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.normalizedCellCostSum =
      ferrersCellCostPotential finish - ferrersCellCostPotential start := by
  induction C with
  | refl =>
      simp [normalizedCellCostSum]
  | @step u v C S ih =>
      have hStep := S.ferrersCellCostPotential_upper_eq_lower_add_cellCost
      change
        C.normalizedCellCostSum + S.edge.fareyCellCost =
          ferrersCellCostPotential v - ferrersCellCostPotential start
      rw [ih, hStep]
      ring

/--
first-passage chain の positive-cost winding normal form。

  q_finish = q_start + G * carryCount - totalCost.
-/
theorem normalized_finish_eq_start_add_gap_mul_carryCount_sub_cellCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    normalizedSeparationDefectInt finish =
      normalizedSeparationDefectInt start +
        (wordTerminalGap start : ℤ) * (C.normalizedCarryCount : ℤ) -
        C.normalizedCellCostSum := by
  induction C with
  | refl =>
      simp [normalizedCarryCount, normalizedCellCostSum]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hStep :=
        S.normalizedStepDelta_eq_gap_mul_carryIndicator_sub_cellCost hUFP
      have hEndpoint :
          normalizedSeparationDefectInt v =
            normalizedSeparationDefectInt u + FerrersStep.normalizedStepDelta u v := by
        unfold FerrersStep.normalizedStepDelta
        ring
      have hEdgeFP : IsFirstPassageWord S.edge.lowerWord := by
        simpa [S.lower_eq] using hUFP
      have hGEdge :=
        S.edge.fareyPacket_G_eq_wordTerminalGap hEdgeFP.2.2
      have hGStart :
          S.edge.toFareyCellPacket.G = (wordTerminalGap start : ℤ) := by
        calc
          S.edge.toFareyCellPacket.G
              = (wordTerminalGap S.edge.lowerWord : ℤ) := hGEdge
          _ = (wordTerminalGap u : ℤ) := by rw [← S.lower_eq]
          _ = (wordTerminalGap start : ℤ) := by
            exact_mod_cast C.wordTerminalGap_eq.symm
      change
        normalizedSeparationDefectInt v =
          normalizedSeparationDefectInt start +
            (wordTerminalGap start : ℤ) *
              ((C.normalizedCarryCount + S.normalizedCarryIndicator : ℕ) : ℤ) -
            (C.normalizedCellCostSum + S.edge.fareyCellCost)
      calc
        normalizedSeparationDefectInt v
            = normalizedSeparationDefectInt u + FerrersStep.normalizedStepDelta u v := hEndpoint
        _ = normalizedSeparationDefectInt u +
              (S.edge.toFareyCellPacket.G *
                  (S.normalizedCarryIndicator : ℤ) - S.edge.fareyCellCost) := by
            rw [hStep]
        _ =
            (normalizedSeparationDefectInt start +
                (wordTerminalGap start : ℤ) * (C.normalizedCarryCount : ℤ) -
                C.normalizedCellCostSum) +
              (S.edge.toFareyCellPacket.G *
                  (S.normalizedCarryIndicator : ℤ) - S.edge.fareyCellCost) := by
            rw [ih]
        _ =
            normalizedSeparationDefectInt start +
              (wordTerminalGap start : ℤ) *
                ((C.normalizedCarryCount + S.normalizedCarryIndicator : ℕ) : ℤ) -
              (C.normalizedCellCostSum + S.edge.fareyCellCost) := by
            rw [hGStart]
            push_cast
            ring

/-- first-passage chain では各 positive integer cell cost が少なくとも1。 -/
theorem stepCount_le_normalizedCellCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    (C.ferrersStepCount : ℤ) ≤ C.normalizedCellCostSum := by
  induction C with
  | refl =>
      simp [ferrersStepCount, normalizedCellCostSum]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hContract : 3 ^ S.edge.oddTotal < S.edge.modulus := by
        have h := hUFP.2.2
        unfold CoefficientContracting at h
        rw [S.lower_eq] at h
        simpa [AdjacentFerrersSwap.modulus] using h
      have hCostPos : 0 < S.edge.fareyCellCost :=
        S.edge.fareyCellCost_pos_of_contracting hContract
      have hCostOne : (1 : ℤ) ≤ S.edge.fareyCellCost := by omega
      change
        ((C.ferrersStepCount + 1 : ℕ) : ℤ) ≤
          C.normalizedCellCostSum + S.edge.fareyCellCost
      push_cast
      linarith

/-- carry count も endpoints だけで決まる。 -/
theorem normalizedCarryCount_chain_independent
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C₁.normalizedCarryCount = C₂.normalizedCarryCount := by
  have hNo := C₁.normalizedNoCarryCount_chain_independent C₂ hStartFP
  have hStep₁ := C₁.normalizedCarryCount_add_noCarryCount_eq_stepCount
  have hStep₂ := C₂.normalizedCarryCount_add_noCarryCount_eq_stepCount
  have hDist₁ := C₁.ferrersStepCount_eq_ferrersDistance
  have hDist₂ := C₂.ferrersStepCount_eq_ferrersDistance
  omega

end FerrersChain

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket

/-- actual boundary -> minimal B chain の carry winding。 -/
noncomputable def carryWinding
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ℕ :=
  M.boundaryToWordChain.normalizedCarryCount

/-- actual boundary -> minimal B の total positive cell cost。 -/
noncomputable def boundaryToWordCellCost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ℤ :=
  M.boundaryToWordChain.normalizedCellCostSum

/--
actual A -> minimal B の exact winding equation。

  q_B = q_A + G * winding - totalCost.
-/
theorem word_normalized_eq_boundary_add_gap_mul_winding_sub_cost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    normalizedSeparationDefectInt M.word =
      normalizedSeparationDefectInt M.actual.cocycle.provenance.boundary +
        (wordTerminalGap M.actual.cocycle.provenance.boundary : ℤ) *
          (M.carryWinding : ℤ) -
        M.boundaryToWordCellCost := by
  exact
    M.boundaryToWordChain.normalized_finish_eq_start_add_gap_mul_carryCount_sub_cellCostSum
      M.actual.cocycle.provenance.boundary_isBoundary.1

/--
A boundary の `q_A <= -1`、minimal B の `q_B >= 0`、各 cell cost >= 1 を合わせる。

  G * carryWinding >= FerrersDistance(A,B) + 1.
-/
theorem ferrersDistance_add_one_le_gap_mul_carryWinding
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    (ferrersDistance M.actual.cocycle.provenance.boundary M.word : ℤ) + 1 ≤
      (wordTerminalGap M.actual.cocycle.provenance.boundary : ℤ) *
        (M.carryWinding : ℤ) := by
  have hEq := M.word_normalized_eq_boundary_add_gap_mul_winding_sub_cost
  have hStart := M.actual.cocycle.boundary_normalized_le_neg_one
  have hFinish : 0 ≤ normalizedSeparationDefectInt M.word := by
    rw [← M.actual_q_cast_eq_word_normalized]
    exact Int.natCast_nonneg M.actual.q
  have hCost :=
    M.boundaryToWordChain.stepCount_le_normalizedCellCostSum
      M.actual.cocycle.provenance.boundary_isBoundary.1
  have hDist := M.boundaryToWordChain.ferrersStepCount_eq_ferrersDistance
  rw [hDist] at hCost
  unfold boundaryToWordCellCost at hEq
  linarith

end MinimalActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
