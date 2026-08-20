import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeIntegralStateWronskian
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelDefectValuation

/-!
# Pure B relative bridge 7: canonical block defect の exact 3-adic propagation

Stage 6 で canonical start state `Z_a` に対し

  2^β_a [Γ_(j+1) B_j - Γ_j B_(j+1)]
    = 3^(a-1) Wcorr_j

を得た。corrected Wronskian は exact signed pure two-power なので、cross term 自身は
exact に `3^(a-1)` まで割れる。

さらに actual raw gap `Γ_j = 2^Q_j - 3^P_j` は `P_j>0` のため 3-adic unit。
ここでは既存の `n ≤ P_j` という制限を外し、任意 `n` について

  IsCoprime (3^n) Γ_j

を証明する。これにより

  3^a | B_(j+1)  =>  ord_3(B_j)     = a-1,
  3^a | B_j      =>  ord_3(B_(j+1)) = a-1

という relative exact propagation が得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `3` と `2` は整数環で coprime。 -/
private theorem relativeBridge_three_two_isCoprime :
    IsCoprime (3 : ℤ) (2 : ℤ) := by
  refine ⟨1, -1, ?_⟩
  norm_num

/-- 第二成分から第一成分の倍数を引いても coprime 性は保存される。 -/
private theorem relativeBridge_isCoprime_sub_mul_right
    {a b c : ℤ}
    (h : IsCoprime a b) :
    IsCoprime a (b - a * c) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u + v * c, v, ?_⟩
  calc
    (u + v * c) * a + v * (b - a * c)
        = u * a + v * b := by ring
    _ = 1 := huv

/--
actual raw gap は relevant index では任意の `3^n` と coprime。

既存補題の `n ≤ P_j` 制限はここでは不要。`P_j>0` により
`3^P_j = 3 * 3^(P_j-1)` と書け、mod 3 では gap は pure two-power になる。
-/
theorem threePow_isCoprime_actualCriticalRawPowerGap
    {j n : ℕ}
    (hj : 9 ≤ j) :
    IsCoprime
      ((3 : ℤ) ^ n)
      (actualCriticalRawPowerGap j) := by
  have hp : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hTwo :
      IsCoprime
        (3 : ℤ)
        ((2 : ℤ) ^ criticalPowerQ j) := by
    exact relativeBridge_three_two_isCoprime.pow_right
  have hThree :
      (3 : ℤ) ^ criticalPowerP j =
        (3 : ℤ) * (3 : ℤ) ^ (criticalPowerP j - 1) := by
    have hExp :
        criticalPowerP j = (criticalPowerP j - 1) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring_nf
    simp
  have hGap :
      IsCoprime
        (3 : ℤ)
        (actualCriticalRawPowerGap j) := by
    unfold actualCriticalRawPowerGap
    rw [hThree]
    exact relativeBridge_isCoprime_sub_mul_right hTwo
  exact hGap.pow_left

/-- `a>0` なら `3^(a-1)` は `3^a` を割る。 -/
private theorem relativeBridge_threePow_pred_dvd_threePow
    {a : ℕ}
    (ha : 0 < a) :
    (3 : ℤ) ^ (a - 1) ∣ (3 : ℤ) ^ a := by
  refine ⟨3, ?_⟩
  have hExp : a = (a - 1) + 1 := by
    omega
  rw [hExp, pow_succ]
  simp

/--
`a>0` なら `3^a` は `3^(a-1) * 2^k` を割らない。
-/
private theorem relativeBridge_not_threePow_dvd_pred_mul_twoPow
    (a k : ℕ)
    (ha : 0 < a) :
    ¬ (3 : ℤ) ^ a ∣
      (3 : ℤ) ^ (a - 1) * (2 : ℤ) ^ k := by
  intro hDiv
  have hCoprime :
      IsCoprime
        ((3 : ℤ) ^ a)
        ((2 : ℤ) ^ k) := by
    exact relativeBridge_three_two_isCoprime.pow
  have hSmallInt :
      (3 : ℤ) ^ a ∣ (3 : ℤ) ^ (a - 1) :=
    hCoprime.dvd_of_dvd_mul_right hDiv
  have hSmallNat :
      (3 : ℕ) ^ a ∣ (3 : ℕ) ^ (a - 1) := by
    exact_mod_cast hSmallInt
  have hLe :
      (3 : ℕ) ^ a ≤ (3 : ℕ) ^ (a - 1) :=
    Nat.le_of_dvd (by positivity) hSmallNat
  have hLt :
      (3 : ℕ) ^ (a - 1) < (3 : ℕ) ^ a := by
    have hExp : a = (a - 1) + 1 := by
      omega
    rw [hExp, pow_succ]
    have hPos : 0 < (3 : ℕ) ^ (a - 1) := by
      positivity
    simp
  omega

namespace PureBProfileObstruction

/--
canonical adjacent cross は exact に `3^(a-1)` まで割れる。

Stage 6 の identity と corrected Wronskian の signed pure-two-power theorem を合成する。
-/
theorem integralCanonicalAdjacentCross_exactThreeAdicOrder
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hj : 9 ≤ j)
    (hRangeJ :
      a + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      a + criticalPowerP (j + 1) <
        criticalPowerP (j + 2)) :
    ExactThreeAdicOrder
      (
        actualCriticalRawPowerGap (j + 1) *
            P.integralCanonicalBlockDefect A j -
          actualCriticalRawPowerGap j *
            P.integralCanonicalBlockDefect A (j + 1)
      )
      (a - 1) := by
  let C : ℤ :=
    actualCriticalRawPowerGap (j + 1) *
        P.integralCanonicalBlockDefect A j -
      actualCriticalRawPowerGap j *
        P.integralCanonicalBlockDefect A (j + 1)
  change ExactThreeAdicOrder C (a - 1)
  have hCross :=
    P.integralCanonicalBlockDefect_adjacentWronskian
      (A := A)
      haPos
      hj
      hRangeJ
      hRangeNext
  change
    (2 : ℤ) ^ beattyIndex a * C =
      (3 : ℤ) ^ (a - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j at hCross
  constructor
  · have hLeftDiv :
        (3 : ℤ) ^ (a - 1) ∣
          (2 : ℤ) ^ beattyIndex a * C := by
      rw [hCross]
      refine ⟨
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j,
        ?_⟩
      ring
    have hCoprime :
        IsCoprime
          ((3 : ℤ) ^ (a - 1))
          ((2 : ℤ) ^ beattyIndex a) := by
      exact relativeBridge_three_two_isCoprime.pow
    exact hCoprime.dvd_of_dvd_mul_left hLeftDiv
  · intro hTooDeep
    have hTooDeepA :
        (3 : ℤ) ^ a ∣ C := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hTooDeep
    have hLeftDeep :
        (3 : ℤ) ^ a ∣
          (2 : ℤ) ^ beattyIndex a * C :=
      dvd_mul_of_dvd_right hTooDeepA _
    rw [hCross] at hLeftDeep
    rcases
        actualCorrectedChristoffelWronskianNext_signed_strongPrecision
          hj with
      hEven | hOdd
    · rw [hEven.2] at hLeftDeep
      have hNeg :
          (3 : ℤ) ^ a ∣
            -((3 : ℤ) ^ (a - 1) *
              (2 : ℤ) ^
                actualCriticalContinuedFractionData.strongPrecision j) := by
        simpa only [mul_neg] using hLeftDeep
      have hPos := dvd_neg.mp hNeg
      exact
        relativeBridge_not_threePow_dvd_pred_mul_twoPow
          a
          (actualCriticalContinuedFractionData.strongPrecision j)
          haPos
          hPos
    · rw [hOdd.2] at hLeftDeep
      exact
        relativeBridge_not_threePow_dvd_pred_mul_twoPow
          a
          (actualCriticalContinuedFractionData.strongPrecision j)
          haPos
          hLeftDeep

/--
next canonical block が `3^a`-deep なら current block は exact `a-1` で止まる。
-/
theorem integralCanonicalBlockDefect_exactThreeAdicOrder_of_next_deep
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hj : 9 ≤ j)
    (hRangeJ :
      a + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      a + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (hDeep :
      (3 : ℤ) ^ a ∣
        P.integralCanonicalBlockDefect A (j + 1)) :
    ExactThreeAdicOrder
      (P.integralCanonicalBlockDefect A j)
      (a - 1) := by
  let Bj : ℤ := P.integralCanonicalBlockDefect A j
  let Bn : ℤ := P.integralCanonicalBlockDefect A (j + 1)
  change (3 : ℤ) ^ a ∣ Bn at hDeep
  change ExactThreeAdicOrder Bj (a - 1)
  have hCross :=
    P.integralCanonicalAdjacentCross_exactThreeAdicOrder
      (A := A)
      haPos
      hj
      hRangeJ
      hRangeNext
  change
    ExactThreeAdicOrder
      (actualCriticalRawPowerGap (j + 1) * Bj -
        actualCriticalRawPowerGap j * Bn)
      (a - 1) at hCross
  constructor
  · have hDeepPred :
        (3 : ℤ) ^ (a - 1) ∣ Bn :=
      (relativeBridge_threePow_pred_dvd_threePow haPos).trans hDeep
    have hSecond :
        (3 : ℤ) ^ (a - 1) ∣
          actualCriticalRawPowerGap j * Bn :=
      dvd_mul_of_dvd_right hDeepPred _
    have hProduct :
        (3 : ℤ) ^ (a - 1) ∣
          actualCriticalRawPowerGap (j + 1) * Bj := by
      have hEq :
          actualCriticalRawPowerGap (j + 1) * Bj =
            (actualCriticalRawPowerGap (j + 1) * Bj -
                actualCriticalRawPowerGap j * Bn) +
              actualCriticalRawPowerGap j * Bn := by
        ring
      rw [hEq]
      exact dvd_add hCross.1 hSecond
    have hCoprime :=
      threePow_isCoprime_actualCriticalRawPowerGap
        (j := j + 1)
        (n := a - 1)
        (by omega)
    exact hCoprime.dvd_of_dvd_mul_left hProduct
  · intro hTooDeep
    have hTooDeepA :
        (3 : ℤ) ^ a ∣ Bj := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hTooDeep
    have hLeft :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap (j + 1) * Bj :=
      dvd_mul_of_dvd_right hTooDeepA _
    have hRight :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap j * Bn :=
      dvd_mul_of_dvd_right hDeep _
    have hCrossDeep :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap (j + 1) * Bj -
            actualCriticalRawPowerGap j * Bn :=
      dvd_sub hLeft hRight
    apply hCross.2
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hCrossDeep

/--
current canonical block が `3^a`-deep なら next block は exact `a-1` で止まる。
-/
theorem integralCanonicalNextBlockDefect_exactThreeAdicOrder_of_current_deep
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hj : 9 ≤ j)
    (hRangeJ :
      a + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      a + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (hDeep :
      (3 : ℤ) ^ a ∣
        P.integralCanonicalBlockDefect A j) :
    ExactThreeAdicOrder
      (P.integralCanonicalBlockDefect A (j + 1))
      (a - 1) := by
  let Bj : ℤ := P.integralCanonicalBlockDefect A j
  let Bn : ℤ := P.integralCanonicalBlockDefect A (j + 1)
  change (3 : ℤ) ^ a ∣ Bj at hDeep
  change ExactThreeAdicOrder Bn (a - 1)
  have hCross :=
    P.integralCanonicalAdjacentCross_exactThreeAdicOrder
      (A := A)
      haPos
      hj
      hRangeJ
      hRangeNext
  change
    ExactThreeAdicOrder
      (actualCriticalRawPowerGap (j + 1) * Bj -
        actualCriticalRawPowerGap j * Bn)
      (a - 1) at hCross
  constructor
  · have hDeepPred :
        (3 : ℤ) ^ (a - 1) ∣ Bj :=
      (relativeBridge_threePow_pred_dvd_threePow haPos).trans hDeep
    have hFirst :
        (3 : ℤ) ^ (a - 1) ∣
          actualCriticalRawPowerGap (j + 1) * Bj :=
      dvd_mul_of_dvd_right hDeepPred _
    have hProduct :
        (3 : ℤ) ^ (a - 1) ∣
          actualCriticalRawPowerGap j * Bn := by
      have hEq :
          actualCriticalRawPowerGap j * Bn =
            actualCriticalRawPowerGap (j + 1) * Bj -
              (actualCriticalRawPowerGap (j + 1) * Bj -
                actualCriticalRawPowerGap j * Bn) := by
        ring
      rw [hEq]
      exact dvd_sub hFirst hCross.1
    have hCoprime :=
      threePow_isCoprime_actualCriticalRawPowerGap
        (j := j)
        (n := a - 1)
        hj
    exact hCoprime.dvd_of_dvd_mul_left hProduct
  · intro hTooDeep
    have hTooDeepA :
        (3 : ℤ) ^ a ∣ Bn := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hTooDeep
    have hLeft :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap (j + 1) * Bj :=
      dvd_mul_of_dvd_right hDeep _
    have hRight :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap j * Bn :=
      dvd_mul_of_dvd_right hTooDeepA _
    have hCrossDeep :
        (3 : ℤ) ^ a ∣
          actualCriticalRawPowerGap (j + 1) * Bj -
            actualCriticalRawPowerGap j * Bn :=
      dvd_sub hLeft hRight
    apply hCross.2
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hCrossDeep

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
