import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnProfileResidualLedger
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ResidualRankTopLedger

/-!
# 有効 winding と residual cost の大域上界

positive-cost ledger では、一つの first-passage Ferrers step の cell cost `C` を
common terminal gap `G` で

  C = G * a + r,   0 <= r < G

と分解する。

ここで

  effectiveWinding = carryIndicator - a

と置くと、一セルごとに

  effectiveWinding <= r

が成り立つ。

理由は三場合だけである。

* no-carry なら `carryIndicator = 0` なので左辺は非正。
* carry かつ `a >= 1` でも左辺は非正。
* carry かつ `a = 0` のときだけ左辺は `1` になるが、
  first-passage cell cost は正なので `C = r >= 1`。

この局所不等式を chain 全体で足し、

  E <= R

を得る。ここで `E` は全 effective winding、`R` は bounded residual cost 総和。
さらに residualized local cocycle

  Delta q = G * effectiveWinding - r

を telescope して

  q_finish = q_start + G * E - R

を得る。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersStep

/--
一つの first-passage Ferrers cell では、
有効 winding は bounded residual cost 以下。
-/
theorem actualEffectiveWinding_le_residualCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.actualEffectiveWinding <=
      (S.actualRankTopResidualCost : ℤ) := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · have hIndicator :=
      S.normalizedCarryIndicator_eq_zero_of_noCarry hNo
    have hQNonneg :
        0 <= (S.actualRankTopCostQuotient : ℤ) := by
      positivity
    have hRNonneg :
        0 <= (S.actualRankTopResidualCost : ℤ) := by
      positivity
    unfold actualEffectiveWinding
    rw [hIndicator]
    norm_num
  · have hIndicator :=
      S.normalizedCarryIndicator_eq_one_of_hasCarry hCarry
    by_cases hQ0 : S.actualRankTopCostQuotient = 0
    · have hEdgeFP : IsFirstPassageWord S.edge.lowerWord :=
        S.edge_lower_firstPassage hLowerFP
      have hContract :
          3 ^ S.edge.oddTotal < S.edge.modulus := by
        have h := hEdgeFP.2.2
        unfold CoefficientContracting at h
        simpa [AdjacentFerrersSwap.modulus] using h
      have hCostPos : 0 < S.edge.fareyCellCost :=
        S.edge.fareyCellCost_pos_of_contracting hContract
      have hCostNatPosZ :
          (0 : ℤ) < (S.edge.fareyCellCost.toNat : ℤ) := by
        rw [← S.fareyCellCost_eq_toNat_int hLowerFP]
        exact hCostPos
      have hCostNatPos : 0 < S.edge.fareyCellCost.toNat := by
        exact_mod_cast hCostNatPosZ
      have hDecomp :
          S.edge.fareyCellCost.toNat =
            S.actualRankTopGap * S.actualRankTopCostQuotient +
              S.actualRankTopResidualCost := by
        simpa [actualRankTopCostQuotient, actualRankTopResidualCost] using
          rankTopCost_eq_gap_mul_quotient_add_residual
            S.actualRankTopGap S.edge.fareyCellCost.toNat
      simp [hQ0] at hDecomp
      have hROne : 1 <= S.actualRankTopResidualCost := by
        omega
      have hROneZ :
          (1 : ℤ) <= (S.actualRankTopResidualCost : ℤ) := by
        exact_mod_cast hROne
      unfold actualEffectiveWinding
      rw [hIndicator, hQ0]
      norm_num
      omega
    · have hQPos : 0 < S.actualRankTopCostQuotient :=
        Nat.pos_of_ne_zero hQ0
      have hQOne :
          (1 : ℤ) <= (S.actualRankTopCostQuotient : ℤ) := by
        exact_mod_cast (show 1 <= S.actualRankTopCostQuotient by omega)
      have hRNonneg :
          0 <= (S.actualRankTopResidualCost : ℤ) := by
        positivity
      unfold actualEffectiveWinding
      rw [hIndicator]
      simp
      linarith

end FerrersStep

namespace FerrersChain

/-- chain 全体の有効 winding の総和。 -/
noncomputable def actualEffectiveWindingSum
    {start finish : ParityWord} :
    FerrersChain start finish -> ℤ
  | .refl _ => 0
  | .step C S =>
      C.actualEffectiveWindingSum + S.actualEffectiveWinding

/--
全 effective winding は
`carryCount - fullGapCostQuotientSum` と exact に一致する。

これはユーザー側の記号

  E = c - A(h)

の chain-level 版。
-/
theorem actualEffectiveWindingSum_eq_carryCount_sub_costQuotientSum
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.actualEffectiveWindingSum =
      (C.normalizedCarryCount : ℤ) -
        (C.actualCostQuotientSum : ℤ) := by
  induction C with
  | refl =>
      simp [actualEffectiveWindingSum, normalizedCarryCount,
        actualCostQuotientSum]
  | @step u v C S ih =>
      change
        C.actualEffectiveWindingSum + S.actualEffectiveWinding =
          (((C.normalizedCarryCount +
              S.normalizedCarryIndicator : ℕ) : ℤ)) -
            (((C.actualCostQuotientSum +
              S.actualRankTopCostQuotient : ℕ) : ℤ))
      rw [ih]
      unfold FerrersStep.actualEffectiveWinding
      push_cast
      ring

/--
residualized cocycle を chain 全体へ telescope する。

  q_finish = q_start + G * E - R.
-/
theorem normalized_finish_eq_start_add_gap_mul_effectiveWindingSum_sub_residualCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    normalizedSeparationDefectInt finish =
      normalizedSeparationDefectInt start +
        (wordTerminalGap start : ℤ) * C.actualEffectiveWindingSum -
        (C.actualResidualCostSum : ℤ) := by
  induction C with
  | refl =>
      simp [actualEffectiveWindingSum, actualResidualCostSum]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hStep :=
        S.normalizedStepDelta_eq_gap_mul_effectiveWinding_sub_residualCost
          hUFP
      have hEndpoint :
          normalizedSeparationDefectInt v =
            normalizedSeparationDefectInt u +
              FerrersStep.normalizedStepDelta u v := by
        unfold FerrersStep.normalizedStepDelta
        ring
      have hGap :
          S.actualRankTopGap = wordTerminalGap start := by
        unfold FerrersStep.actualRankTopGap
        calc
          wordTerminalGap S.edge.lowerWord
              = wordTerminalGap u := by
                  rw [← S.lower_eq]
          _ = wordTerminalGap start := C.wordTerminalGap_eq.symm
      change
        normalizedSeparationDefectInt v =
          normalizedSeparationDefectInt start +
            (wordTerminalGap start : ℤ) *
              (C.actualEffectiveWindingSum + S.actualEffectiveWinding) -
            (((C.actualResidualCostSum +
              S.actualRankTopResidualCost : ℕ) : ℤ))
      calc
        normalizedSeparationDefectInt v
            = normalizedSeparationDefectInt u +
                FerrersStep.normalizedStepDelta u v := hEndpoint
        _ = normalizedSeparationDefectInt u +
              ((S.actualRankTopGap : ℤ) * S.actualEffectiveWinding -
                (S.actualRankTopResidualCost : ℤ)) := by
              rw [hStep]
        _ =
            (normalizedSeparationDefectInt start +
                (wordTerminalGap start : ℤ) *
                  C.actualEffectiveWindingSum -
                (C.actualResidualCostSum : ℤ)) +
              ((S.actualRankTopGap : ℤ) * S.actualEffectiveWinding -
                (S.actualRankTopResidualCost : ℤ)) := by
              rw [ih]
        _ =
            normalizedSeparationDefectInt start +
              (wordTerminalGap start : ℤ) *
                (C.actualEffectiveWindingSum + S.actualEffectiveWinding) -
              (((C.actualResidualCostSum +
                S.actualRankTopResidualCost : ℕ) : ℤ)) := by
              rw [hGap]
              push_cast
              ring

/--
chain 全体でも有効 winding は residual cost 総和以下。

  E <= R.
-/
theorem actualEffectiveWindingSum_le_actualResidualCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C.actualEffectiveWindingSum <=
      (C.actualResidualCostSum : ℤ) := by
  induction C with
  | refl =>
      simp [actualEffectiveWindingSum, actualResidualCostSum]
  | @step u v C S ih =>
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hIH := ih
      have hStep :=
        S.actualEffectiveWinding_le_residualCost hUFP
      change
        C.actualEffectiveWindingSum + S.actualEffectiveWinding <=
          (((C.actualResidualCostSum +
            S.actualRankTopResidualCost : ℕ) : ℤ))
      push_cast
      linarith

/--
endpoint 差は bounded residual cost だけで上から抑えられる。

  q_finish - q_start <= (G - 1) * R.

carry history と full-gap quotient は右辺から消える。
-/
theorem normalized_endpoint_difference_le_gap_sub_one_mul_residualCostSum
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    normalizedSeparationDefectInt finish -
        normalizedSeparationDefectInt start <=
      ((wordTerminalGap start : ℤ) - 1) *
        (C.actualResidualCostSum : ℤ) := by
  have hExact :=
    C.normalized_finish_eq_start_add_gap_mul_effectiveWindingSum_sub_residualCostSum
      hStartFP
  have hE :=
    C.actualEffectiveWindingSum_le_actualResidualCostSum hStartFP
  have hMul :
      (wordTerminalGap start : ℤ) * C.actualEffectiveWindingSum <=
        (wordTerminalGap start : ℤ) *
          (C.actualResidualCostSum : ℤ) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  calc
    normalizedSeparationDefectInt finish -
          normalizedSeparationDefectInt start
        =
      (wordTerminalGap start : ℤ) * C.actualEffectiveWindingSum -
        (C.actualResidualCostSum : ℤ) := by
          linarith
    _ <=
      (wordTerminalGap start : ℤ) *
          (C.actualResidualCostSum : ℤ) -
        (C.actualResidualCostSum : ℤ) := by
          exact sub_le_sub_right hMul _
    _ =
      ((wordTerminalGap start : ℤ) - 1) *
        (C.actualResidualCostSum : ℤ) := by
          ring

end FerrersChain

end CSTMicro
end Collatz2
