import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersEffectiveWindingBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersZeroStartSanity

/-!
# RecordFerrers 4A/4B: generic start interval 版

旧 4A/4B の `RankRecordDecomposition w 0` specialization を、
任意の positive start index `a` から terminal までの decomposition

  D : RankRecordDecomposition w a

へ一般化する。

重要なのは、`a ≠ 0` では final profile 全体と比較してはいけない点である。
record blocks が覆うのは

  [a, a + D.lengths.sum)

だけなので、cell-level 側も同じ interval に制限する。

このファイルでは

* interval raw cell cost,
* interval full-gap quotient,
* interval residual cost,
* interval residual lambda

と、generic-start record blocks の量を exact に比較する。

これにより 4A の

  A_record = A_interval + kappa
  R_interval = G*kappa + R_record

および 4B の

  L_interval
    = 3*kappa + L_record + Delta_record

を start index に依存せず保持する。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

/-! ## 1. cell-level interval quantities -/

/-- rank interval `[a,a+n)` の full-gap quotient 総和。 -/
def columnProfileCostQuotientInterval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t =>
      Finset.sum (Finset.range (h (a + t)))
        (fun j => columnLayerCostQuotient H m (a + t) j))

/-- rank interval `[a,a+n)` の residual lambda 総和。 -/
def columnProfileResidualLambdaInterval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t =>
      Finset.sum (Finset.range (h (a + t)))
        (fun j => columnLayerResidualLambda H m (a + t) j))

/--
一つの column の raw cell cost は、その column の quotient / residual に exact 分解する。
-/
theorem columnProfileCellCostColumn_eq_gap_mul_quotient_add_residual
    (H m : ℕ)
    (h : ℕ → ℕ)
    (k : ℕ) :
    columnProfileCellCostColumn H m h k =
      columnLayerGap H m *
          Finset.sum (Finset.range (h k))
            (fun j => columnLayerCostQuotient H m k j) +
        Finset.sum (Finset.range (h k))
          (fun j => columnLayerResidualCost H m k j) := by
  unfold columnProfileCellCostColumn
  calc
    Finset.sum (Finset.range (h k))
        (fun j => columnLayerCellCostNat H m k j)
        =
      Finset.sum (Finset.range (h k))
        (fun j =>
          columnLayerGap H m * columnLayerCostQuotient H m k j +
            columnLayerResidualCost H m k j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simpa [columnLayerCostQuotient, columnLayerResidualCost] using
            (rankTopCost_eq_gap_mul_quotient_add_residual
              (columnLayerGap H m)
              (columnLayerCellCostNat H m k j))
    _ =
      Finset.sum (Finset.range (h k))
          (fun j =>
            columnLayerGap H m * columnLayerCostQuotient H m k j) +
        Finset.sum (Finset.range (h k))
          (fun j => columnLayerResidualCost H m k j) := by
            exact Finset.sum_add_distrib
    _ =
      columnLayerGap H m *
          Finset.sum (Finset.range (h k))
            (fun j => columnLayerCostQuotient H m k j) +
        Finset.sum (Finset.range (h k))
          (fun j => columnLayerResidualCost H m k j) := by
            rw [Finset.mul_sum]

/--
4A の cell-level Euclid decomposition の interval 版。

  C[a,a+n)
    = G * A[a,a+n) + R[a,a+n).
-/
theorem columnProfileCellCostInterval_eq_gap_mul_quotientInterval_add_residualInterval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) :
    columnProfileCellCostInterval H m h a n =
      columnLayerGap H m *
          columnProfileCostQuotientInterval H m h a n +
        columnProfileResidualCostInterval H m h a n := by
  unfold columnProfileCellCostInterval
    columnProfileCostQuotientInterval
    columnProfileResidualCostInterval
  calc
    Finset.sum (Finset.range n)
        (fun t => columnProfileCellCostColumn H m h (a + t))
        =
      Finset.sum (Finset.range n)
        (fun t =>
          columnLayerGap H m *
              Finset.sum (Finset.range (h (a + t)))
                (fun j => columnLayerCostQuotient H m (a + t) j) +
            Finset.sum (Finset.range (h (a + t)))
              (fun j => columnLayerResidualCost H m (a + t) j)) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact
            columnProfileCellCostColumn_eq_gap_mul_quotient_add_residual
              H m h (a + t)
    _ =
      Finset.sum (Finset.range n)
          (fun t =>
            columnLayerGap H m *
              Finset.sum (Finset.range (h (a + t)))
                (fun j => columnLayerCostQuotient H m (a + t) j)) +
        Finset.sum (Finset.range n)
          (fun t =>
            Finset.sum (Finset.range (h (a + t)))
              (fun j => columnLayerResidualCost H m (a + t) j)) := by
            exact Finset.sum_add_distrib
    _ =
      columnLayerGap H m *
          Finset.sum (Finset.range n)
            (fun t =>
              Finset.sum (Finset.range (h (a + t)))
                (fun j => columnLayerCostQuotient H m (a + t) j)) +
        Finset.sum (Finset.range n)
          (fun t =>
            Finset.sum (Finset.range (h (a + t)))
              (fun j => columnLayerResidualCost H m (a + t) j)) := by
            rw [Finset.mul_sum]

/-- quotient interval は隣接 interval に対して exact additive。 -/
theorem columnProfileCostQuotientInterval_add
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a r s : ℕ) :
    columnProfileCostQuotientInterval H m h a (r + s) =
      columnProfileCostQuotientInterval H m h a r +
        columnProfileCostQuotientInterval H m h (a + r) s := by
  unfold columnProfileCostQuotientInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.add_assoc]

/-- residual lambda interval も隣接 interval に対して exact additive。 -/
theorem columnProfileResidualLambdaInterval_add
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a r s : ℕ) :
    columnProfileResidualLambdaInterval H m h a (r + s) =
      columnProfileResidualLambdaInterval H m h a r +
        columnProfileResidualLambdaInterval H m h (a + r) s := by
  unfold columnProfileResidualLambdaInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.add_assoc]

end CSTMicro

namespace Word

open CSTMicro

namespace RankRecordDecomposition

/-! ## 2. generic-start 4A -/

/-- generic start `a` から record skeleton に沿って取る block raw cost list。 -/
def profileBlockCostsFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : List ℕ :=
  recordProfileBlockCosts H (oddSteps w) h a D.lengths

/-- generic-start decomposition の record block 数。 -/
def profileRecordCountFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a) : ℕ :=
  D.lengths.length

/-- generic-start block quotient sum。 -/
def profileBlockCostQuotientSumFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockCostQuotientSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCostsFrom H h)

/-- generic-start block residual cost sum。 -/
def profileBlockResidualCostSumFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockResidualCostSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCostsFrom H h)

/-- generic-start block residual lambda sum。 -/
def profileBlockResidualLambdaSumFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockResidualLambdaSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCostsFrom H h)

/-- generic-start block full lambda sum。 -/
def profileBlockFullLambdaSumFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockFullLambdaSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCostsFrom H h)

/-- block cost list の長さは skeleton の block 数。 -/
theorem profileBlockCostsFrom_length
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) :
    (D.profileBlockCostsFrom H h).length =
      D.profileRecordCountFrom := by
  unfold profileBlockCostsFrom profileRecordCountFrom
  exact
    recordProfileBlockCosts_length
      H (oddSteps w) h a D.lengths

/--
generic-start block raw cost の総和は、同じ covered interval の raw cost。
-/
theorem profileBlockCostsFrom_sum_eq_interval
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) :
    (D.profileBlockCostsFrom H h).sum =
      columnProfileCellCostInterval
        H (oddSteps w) h a D.lengths.sum := by
  unfold profileBlockCostsFrom
  exact
    recordProfileBlockCosts_sum_eq_interval
      H (oddSteps w) h a D.lengths

/--
generic-start block Euclid decomposition。

  C_interval = G*A_record + R_record.
-/
theorem coveredIntervalCellCost_eq_gap_mul_recordQuotientFrom_add_recordResidualFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) :
    columnProfileCellCostInterval
        H (oddSteps w) h a D.lengths.sum =
      columnLayerGap H (oddSteps w) *
          D.profileBlockCostQuotientSumFrom H h +
        D.profileBlockResidualCostSumFrom H h := by
  have hList :=
    listCostSum_eq_gap_mul_quotientSum_add_residualSum
      (columnLayerGap H (oddSteps w))
      (D.profileBlockCostsFrom H h)
  rw [D.profileBlockCostsFrom_sum_eq_interval H h] at hList
  simpa [
    profileBlockCostQuotientSumFrom,
    profileBlockResidualCostSumFrom
  ] using hList

/--
generic-start 4A の monotonicity:
block residual は同じ covered interval の cell residual 以下。
-/
theorem profileBlockResidualCostSumFrom_le_intervalResidualCostSum
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) :
    D.profileBlockResidualCostSumFrom H h ≤
      columnProfileResidualCostInterval
        H (oddSteps w) h a D.lengths.sum := by
  have hBound :=
    recordProfileBlockResidualSum_le_intervalResidual
      H (oddSteps w) h a D.lengths
  simpa [
    profileBlockResidualCostSumFrom,
    profileBlockCostsFrom
  ] using hBound

/--
generic-start record-count strict bound。

  R_record < G * (#records).
-/
theorem profileBlockResidualCostSumFrom_lt_gap_mul_recordCountFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    D.profileBlockResidualCostSumFrom H h <
      columnLayerGap H (oddSteps w) *
        D.profileRecordCountFrom := by
  have hLengthsNe : D.lengths ≠ [] := D.lengths_nonempty
  have hCostsNe : D.profileBlockCostsFrom H h ≠ [] := by
    intro hNil
    have hLenEq := D.profileBlockCostsFrom_length H h
    rw [hNil] at hLenEq
    have hZero : D.lengths.length = 0 := by
      simpa [profileRecordCountFrom] using hLenEq.symm
    exact hLengthsNe (List.length_eq_zero_iff.mp hZero)
  have hStrict :=
    recordBlockResidualCostSum_lt_gap_mul_length
      hGap hCostsNe
  rw [D.profileBlockCostsFrom_length H h] at hStrict
  simpa [profileBlockResidualCostSumFrom] using hStrict

/--
generic-start 4A の coarsening carry。

  A_record = A_interval + kappa
  R_interval = G*kappa + R_record.
-/
theorem exists_recordCoarseningCarryFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    ∃ kappa : ℕ,
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa ∧
      columnProfileResidualCostInterval
          H (oddSteps w) h a D.lengths.sum =
        columnLayerGap H (oddSteps w) * kappa +
          D.profileBlockResidualCostSumFrom H h := by
  let G := columnLayerGap H (oddSteps w)
  let A :=
    columnProfileCostQuotientInterval
      H (oddSteps w) h a D.lengths.sum
  let R :=
    columnProfileResidualCostInterval
      H (oddSteps w) h a D.lengths.sum
  let Arec := D.profileBlockCostQuotientSumFrom H h
  let Rrec := D.profileBlockResidualCostSumFrom H h
  have hCell :=
    columnProfileCellCostInterval_eq_gap_mul_quotientInterval_add_residualInterval
      H (oddSteps w) h a D.lengths.sum
  have hRecord :=
    D.coveredIntervalCellCost_eq_gap_mul_recordQuotientFrom_add_recordResidualFrom
      H h
  have hEq : G * A + R = G * Arec + Rrec := by
    dsimp [G, A, R, Arec, Rrec]
    rw [← hCell, ← hRecord]
  have hRle : Rrec ≤ R := by
    dsimp [Rrec, R]
    exact D.profileBlockResidualCostSumFrom_le_intervalResidualCostSum H h
  have hAle : A ≤ Arec := by
    by_contra hnot
    have hlt : Arec < A := by
      omega
    have hMul : G * Arec < G * A :=
      Nat.mul_lt_mul_of_pos_left hlt hGap
    have h1 : G * Arec + Rrec < G * A + Rrec :=
      Nat.add_lt_add_right hMul Rrec
    have h2 : G * A + Rrec ≤ G * A + R :=
      Nat.add_le_add_left hRle (G * A)
    have hContr : G * Arec + Rrec < G * A + R :=
      lt_of_lt_of_le h1 h2
    rw [hEq] at hContr
    exact (Nat.lt_irrefl _ hContr)
  let kappa := Arec - A
  have hAeq : Arec = A + kappa := by
    dsimp [kappa]
    omega
  have hReq : R = G * kappa + Rrec := by
    have hEq' := hEq
    rw [hAeq, Nat.mul_add] at hEq'
    have hEq'' :
        G * A + R =
          G * A + (G * kappa + Rrec) := by
      simpa [Nat.add_assoc] using hEq'
    exact Nat.add_left_cancel hEq''
  refine ⟨kappa, ?_, ?_⟩
  · simpa [Arec, A] using hAeq
  · simpa [R, G, Rrec] using hReq

/-! ## 3. generic-start 4B -/

/-- generic-start record residual lambda は `3 * recordCount` 以下。 -/
theorem profileBlockResidualLambdaSumFrom_le_three_mul_recordCountFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    D.profileBlockResidualLambdaSumFrom H h ≤
      3 * D.profileRecordCountFrom := by
  have hBound :=
    recordBlockResidualLambdaSum_le_three_mul_length
      hGap (D.profileBlockCostsFrom H h)
  rw [D.profileBlockCostsFrom_length H h] at hBound
  simpa [profileBlockResidualLambdaSumFrom] using hBound

/-- generic-start block full lambda の exact decomposition。 -/
theorem profileBlockFullLambdaSumFrom_eq_three_mul_recordQuotientFrom_add_recordResidualLambdaFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    D.profileBlockFullLambdaSumFrom H h =
      3 * D.profileBlockCostQuotientSumFrom H h +
        D.profileBlockResidualLambdaSumFrom H h := by
  exact
    recordBlockFullLambdaSum_eq_three_mul_quotientSum_add_residualLambdaSum
      hGap (D.profileBlockCostsFrom H h)

/--
generic-start lambda coarsening defect。

cell-level と block-level を必ず同じ covered interval で比較する。
-/
def profileLambdaCoarseningDefectZFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  3 *
      (columnProfileCostQuotientInterval
        H (oddSteps w) h a D.lengths.sum : ℤ) +
    (columnProfileResidualLambdaInterval
      H (oddSteps w) h a D.lengths.sum : ℤ) -
    (3 * (D.profileBlockCostQuotientSumFrom H h : ℤ) +
      (D.profileBlockResidualLambdaSumFrom H h : ℤ))

/--
generic-start 4B の exact lambda rewrite。

  L_interval
    = 3*kappa + L_record + Delta_record.
-/
theorem cellResidualLambdaInterval_eq_three_mul_kappa_add_recordResidualLambdaFrom_add_defect
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa) :
    (columnProfileResidualLambdaInterval
        H (oddSteps w) h a D.lengths.sum : ℤ) =
      3 * (kappa : ℤ) +
        (D.profileBlockResidualLambdaSumFrom H h : ℤ) +
        D.profileLambdaCoarseningDefectZFrom H h := by
  unfold profileLambdaCoarseningDefectZFrom
  have hAZ := congrArg (fun n : ℕ => (n : ℤ)) hA
  push_cast at hAZ
  rw [hAZ]
  ring

/--
generic-start 4A/4B normal form を一度に返す checkpoint。
-/
theorem exists_recordLambdaCoarseningNormalFormFrom
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    ∃ kappa : ℕ,
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (oddSteps w) h a D.lengths.sum +
          kappa ∧
      columnProfileResidualCostInterval
          H (oddSteps w) h a D.lengths.sum =
        columnLayerGap H (oddSteps w) * kappa +
          D.profileBlockResidualCostSumFrom H h ∧
      (columnProfileResidualLambdaInterval
          H (oddSteps w) h a D.lengths.sum : ℤ) =
        3 * (kappa : ℤ) +
          (D.profileBlockResidualLambdaSumFrom H h : ℤ) +
          D.profileLambdaCoarseningDefectZFrom H h := by
  obtain ⟨kappa, hA, hR⟩ :=
    D.exists_recordCoarseningCarryFrom H h hGap
  refine ⟨kappa, hA, hR, ?_⟩
  exact
    D.cellResidualLambdaInterval_eq_three_mul_kappa_add_recordResidualLambdaFrom_add_defect
      H h hA

end RankRecordDecomposition

end Word
end Collatz2
