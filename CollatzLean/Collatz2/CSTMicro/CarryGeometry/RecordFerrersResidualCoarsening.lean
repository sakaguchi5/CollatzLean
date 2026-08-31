import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.QuantitativeBoundaryAResidualBound
import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization

/-!
# RecordFerrers による residual cost の block coarsening

前段では critical boundary から minimal bad word までの actual Ferrers chain に対して

  q_B = q_A + G * E - R(h)

および

  E <= R(h)

を得た。

このファイルでは次の段階として、final PureB profile の cell cost を
`RankRecordDecomposition` の record block ごとにまとめる。

一つの record block に含まれる raw cell cost の総和を `C_b` とし、common gap `G` で

  C_b = G * A_b + R_b,
  0 <= R_b < G

と Euclid 分解する。

全 record block を足した量を

  A_record = sum A_b,
  R_record = sum R_b

とする。このとき

  R_record < G * (#records)

が得られる。

さらに cell ごとの Euclid 分解

  C_total = G * A(h) + R(h)

と block ごとの分解を比較すると、ある `kappa : Nat` が存在して

  A_record = A(h) + kappa,
  R(h) = G * kappa + R_record

となる。

したがって block coarsening は residual budget を悪化させず、

  R_record <= R(h)

である。

ここでは effective winding の block-level bound は主張しない。
任意の block 化ではその種の不等式は偽になり得るため、そこは次段の
RecordFerrers 固有の幾何として分離する。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

/-! ## 1. profile raw cell cost -/

/--
一つの rank column `k` に積まれた全 layer の raw cell cost。
-/
def columnProfileCellCostColumn
    (H m : ℕ)
    (h : ℕ → ℕ)
    (k : ℕ) : ℕ :=
  Finset.sum (Finset.range (h k))
    (fun j => columnLayerCellCostNat H m k j)

/--
final profile 全体の raw cell cost 総和。
-/
def columnProfileCellCostSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  columnProfileSum m h
    (fun k j => columnLayerCellCostNat H m k j)

/--
一 cell の raw cost の Euclid decomposition。
-/
theorem columnLayerCellCostNat_eq_gap_mul_quotient_add_residual
    (H m k j : ℕ) :
    columnLayerCellCostNat H m k j =
      columnLayerGap H m * columnLayerCostQuotient H m k j +
        columnLayerResidualCost H m k j := by
  simpa [columnLayerCostQuotient, columnLayerResidualCost] using
    rankTopCost_eq_gap_mul_quotient_add_residual
      (columnLayerGap H m)
      (columnLayerCellCostNat H m k j)

/--
profile sum は cell ごとの和に対して加法的。
-/
theorem columnProfileSum_add
    {α : Type*}
    [AddCommMonoid α]
    (m : ℕ)
    (h : ℕ → ℕ)
    (f g : ℕ → ℕ → α) :
    columnProfileSum m h (fun k j => f k j + g k j) =
      columnProfileSum m h f + columnProfileSum m h g := by
  unfold columnProfileSum
  calc
    Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k))
            (fun j => f k j + g k j))
        =
      Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k)) (fun j => f k j) +
            Finset.sum (Finset.range (h k)) (fun j => g k j)) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact Finset.sum_add_distrib
    _ =
      Finset.sum (Finset.range m)
          (fun k => Finset.sum (Finset.range (h k)) (fun j => f k j)) +
        Finset.sum (Finset.range m)
          (fun k => Finset.sum (Finset.range (h k)) (fun j => g k j)) := by
            exact Finset.sum_add_distrib

/--
Nat-valued profile sum から共通係数を外へ出す。
-/
theorem columnProfileSum_nat_mul_left
    (c m : ℕ)
    (h : ℕ → ℕ)
    (f : ℕ → ℕ → ℕ) :
    columnProfileSum m h (fun k j => c * f k j) =
      c * columnProfileSum m h f := by
  unfold columnProfileSum
  calc
    Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k))
            (fun j => c * f k j))
        =
      Finset.sum (Finset.range m)
        (fun k => c *
          Finset.sum (Finset.range (h k)) (fun j => f k j)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
    _ = c *
      Finset.sum (Finset.range m)
        (fun k => Finset.sum (Finset.range (h k)) (fun j => f k j)) := by
          rw [Finset.mul_sum]

/--
cell-level の full-gap quotient / residual decomposition を profile 全体へ足した exact identity。

  C_total = G * A(h) + R(h).
-/
theorem columnProfileCellCostSum_eq_gap_mul_quotientSum_add_residualSum
    (H m : ℕ)
    (h : ℕ → ℕ) :
    columnProfileCellCostSum H m h =
      columnLayerGap H m * columnProfileCostQuotientSum H m h +
        columnProfileResidualCostSum H m h := by
  let G := columnLayerGap H m
  let q : ℕ → ℕ → ℕ := fun k j => columnLayerCostQuotient H m k j
  let r : ℕ → ℕ → ℕ := fun k j => columnLayerResidualCost H m k j
  calc
    columnProfileCellCostSum H m h =
        columnProfileSum m h
          (fun k j => G * q k j + r k j) := by
            unfold columnProfileCellCostSum columnProfileSum
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro j hj
            simpa [G, q, r] using
              columnLayerCellCostNat_eq_gap_mul_quotient_add_residual
                H m k j
    _ =
        columnProfileSum m h (fun k j => G * q k j) +
          columnProfileSum m h r := by
            exact columnProfileSum_add m h
              (fun k j => G * q k j) r
    _ =
        G * columnProfileSum m h q +
          columnProfileSum m h r := by
            rw [columnProfileSum_nat_mul_left]
    _ =
        columnLayerGap H m * columnProfileCostQuotientSum H m h +
          columnProfileResidualCostSum H m h := by
            rfl

/-! ## 2. rank interval と record block の raw cost -/

/--
rank interval `[a, a+n)` に含まれる profile raw cell cost。
-/
def columnProfileCellCostInterval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t => columnProfileCellCostColumn H m h (a + t))

/--
同じ rank interval に含まれる cell-level residual cost。
-/
def columnProfileResidualCostInterval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t =>
      Finset.sum (Finset.range (h (a + t)))
        (fun j => columnLayerResidualCost H m (a + t) j))

/-- raw cost interval は隣接区間で exact に加法的。 -/
theorem columnProfileCellCostInterval_add
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a r s : ℕ) :
    columnProfileCellCostInterval H m h a (r + s) =
      columnProfileCellCostInterval H m h a r +
        columnProfileCellCostInterval H m h (a + r) s := by
  unfold columnProfileCellCostInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.add_assoc]

/-- residual interval も隣接区間で exact に加法的。 -/
theorem columnProfileResidualCostInterval_add
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a r s : ℕ) :
    columnProfileResidualCostInterval H m h a (r + s) =
      columnProfileResidualCostInterval H m h a r +
        columnProfileResidualCostInterval H m h (a + r) s := by
  unfold columnProfileResidualCostInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.add_assoc]

/-- start `0` の full interval は profile raw cost 全体。 -/
theorem columnProfileCellCostInterval_zero_full
    (H m : ℕ)
    (h : ℕ → ℕ) :
    columnProfileCellCostInterval H m h 0 m =
      columnProfileCellCostSum H m h := by
  unfold columnProfileCellCostInterval columnProfileCellCostColumn
    columnProfileCellCostSum columnProfileSum
  simp

/-- start `0` の full residual interval は `R(h)`。 -/
theorem columnProfileResidualCostInterval_zero_full
    (H m : ℕ)
    (h : ℕ → ℕ) :
    columnProfileResidualCostInterval H m h 0 m =
      columnProfileResidualCostSum H m h := by
  unfold columnProfileResidualCostInterval
    columnProfileResidualCostSum columnProfileSum
  simp

/-! ## 3. generic record-length skeleton に沿った block cost -/

/--
record length 列に沿って raw profile cost を block ごとの list にする。
-/
def recordProfileBlockCosts
    (H m : ℕ)
    (h : ℕ → ℕ) :
    ℕ → List ℕ → List ℕ
  | _a, [] => []
  | a, r :: rs =>
      columnProfileCellCostInterval H m h a r ::
        recordProfileBlockCosts H m h (a + r) rs

/-- block cost list の長さは record skeleton の長さと同じ。 -/
theorem recordProfileBlockCosts_length
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) :
    (recordProfileBlockCosts H m h a rs).length = rs.length := by
  induction rs generalizing a with
  | nil => simp [recordProfileBlockCosts]
  | cons r rs ih =>
      simp [recordProfileBlockCosts, ih]

/--
block raw cost を全て足すと、skeleton 全長に対応する一つの interval costへ telescope する。
-/
theorem recordProfileBlockCosts_sum_eq_interval
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) :
    (recordProfileBlockCosts H m h a rs).sum =
      columnProfileCellCostInterval H m h a rs.sum := by
  induction rs generalizing a with
  | nil => simp [recordProfileBlockCosts, columnProfileCellCostInterval]
  | cons r rs ih =>
      simp only [recordProfileBlockCosts, List.sum_cons]
      rw [ih]
      symm
      exact columnProfileCellCostInterval_add H m h a r rs.sum

/-- block cost list の quotient sum。 -/
def recordBlockCostQuotientSum
    (G : ℕ)
    (costs : List ℕ) : ℕ :=
  (costs.map (fun C => rankTopCostQuotient G C)).sum

/-- block cost list の residual sum。 -/
def recordBlockResidualCostSum
    (G : ℕ)
    (costs : List ℕ) : ℕ :=
  (costs.map (fun C => rankTopResidualCost G C)).sum

/--
block list 全体でも Euclid decomposition は exact に telescope する。
-/
theorem listCostSum_eq_gap_mul_quotientSum_add_residualSum
    (G : ℕ)
    (costs : List ℕ) :
    costs.sum =
      G * recordBlockCostQuotientSum G costs +
        recordBlockResidualCostSum G costs := by
  induction costs with
  | nil =>
      simp [recordBlockCostQuotientSum, recordBlockResidualCostSum]
  | cons C costs ih =>
      have hC := rankTopCost_eq_gap_mul_quotient_add_residual G C
      simp only [List.sum_cons, recordBlockCostQuotientSum,
        recordBlockResidualCostSum, List.map_cons] at ih ⊢
      conv_lhs =>
        rw [hC, ih]
      ring


/--
各 block residual は `G-1` 以下なので、総 residual は
`(G-1) * blockCount` 以下。
-/
theorem recordBlockResidualCostSum_le_gap_sub_one_mul_length
    {G : ℕ}
    (hG : 0 < G)
    (costs : List ℕ) :
    recordBlockResidualCostSum G costs ≤
      (G - 1) * costs.length := by
  induction costs with
  | nil =>
      simp [recordBlockResidualCostSum]
  | cons C costs ih =>
      have hRlt : rankTopResidualCost G C < G :=
        rankTopResidualCost_lt_gap hG
      have hRle : rankTopResidualCost G C ≤ G - 1 := by
        omega
      simp only [recordBlockResidualCostSum, List.map_cons,
        List.sum_cons, List.length_cons]
      calc
        rankTopResidualCost G C +
              (costs.map (fun C => rankTopResidualCost G C)).sum
            ≤
          (G - 1) + (G - 1) * costs.length := by
            exact Nat.add_le_add hRle ih
        _ = (G - 1) * (costs.length + 1) := by ring

/--
nonempty block list では strict な record-count bound

  R_record < G * (#blocks)

を得る。
-/
theorem recordBlockResidualCostSum_lt_gap_mul_length
    {G : ℕ}
    (hG : 0 < G)
    {costs : List ℕ}
    (hNonempty : costs ≠ []) :
    recordBlockResidualCostSum G costs < G * costs.length := by
  have hLe := recordBlockResidualCostSum_le_gap_sub_one_mul_length hG costs
  have hLenPos : 0 < costs.length := List.length_pos_iff.mpr hNonempty
  have hGapSub : G - 1 < G := by omega
  have hMul : (G - 1) * costs.length < G * costs.length :=
    Nat.mul_lt_mul_of_pos_right hGapSub hLenPos
  exact lt_of_le_of_lt hLe hMul

/-! ## 4. block residual は cell residual を超えない -/

/-- residual は加法に対して subadditive。 -/
theorem rankTopResidualCost_add_le
    (G x y : ℕ) :
    rankTopResidualCost G (x + y) ≤
      rankTopResidualCost G x + rankTopResidualCost G y := by
  unfold rankTopResidualCost
  rw [Nat.add_mod]
  exact Nat.mod_le _ _

/-- finite sum の residual は residual の和以下。 -/
theorem rankTopResidualCost_finsetSum_le_sum_residual
    {ι : Type*}
    (G : ℕ)
    (s : Finset ι)
    (f : ι → ℕ) :
    rankTopResidualCost G (Finset.sum s f) ≤
      Finset.sum s (fun i => rankTopResidualCost G (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rankTopResidualCost]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans
        (rankTopResidualCost_add_le G (f a) (Finset.sum s f))
        (Nat.add_le_add_left ih _)

/--
一つの rank interval を block としてまとめた residual は、
その interval 内の cell-level residual の和以下。
-/
theorem recordBlockResidualCost_le_cellResidualInterval
    {H m : ℕ}
    (h : ℕ → ℕ)
    (a n : ℕ) :
    rankTopResidualCost
        (columnLayerGap H m)
        (columnProfileCellCostInterval H m h a n) ≤
      columnProfileResidualCostInterval H m h a n := by
  unfold columnProfileCellCostInterval columnProfileResidualCostInterval
  let G := columnLayerGap H m
  let colCost : ℕ → ℕ :=
    fun t => columnProfileCellCostColumn H m h (a + t)
  have hOuter :=
    rankTopResidualCost_finsetSum_le_sum_residual
      G (Finset.range n) colCost
  refine le_trans hOuter ?_
  apply Finset.sum_le_sum
  intro t ht
  unfold colCost columnProfileCellCostColumn
  exact
    rankTopResidualCost_finsetSum_le_sum_residual
      G (Finset.range (h (a + t)))
        (fun j => columnLayerCellCostNat H m (a + t) j)

/--
record skeleton 全体の block residual は、同じ rank interval の cell residual 以下。
-/
theorem recordProfileBlockResidualSum_le_intervalResidual
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) :
    recordBlockResidualCostSum
        (columnLayerGap H m)
        (recordProfileBlockCosts H m h a rs) ≤
      columnProfileResidualCostInterval H m h a rs.sum := by
  induction rs generalizing a with
  | nil =>
      simp [recordProfileBlockCosts, recordBlockResidualCostSum,
        columnProfileResidualCostInterval]
  | cons r rs ih =>
      simp only [recordProfileBlockCosts, recordBlockResidualCostSum,
        List.map_cons, List.sum_cons]
      have hHead :=
        recordBlockResidualCost_le_cellResidualInterval
          (H := H) (m := m) h a r
      have hTail := ih (a + r)
      calc
        rankTopResidualCost (columnLayerGap H m)
              (columnProfileCellCostInterval H m h a r) +
            recordBlockResidualCostSum
              (columnLayerGap H m)
              (recordProfileBlockCosts H m h (a + r) rs)
            ≤
          columnProfileResidualCostInterval H m h a r +
            columnProfileResidualCostInterval H m h (a + r) rs.sum := by
              exact Nat.add_le_add hHead hTail
        _ = columnProfileResidualCostInterval H m h a (r + rs.sum) := by
              symm
              exact columnProfileResidualCostInterval_add H m h a r rs.sum
        _ = columnProfileResidualCostInterval H m h a (r :: rs).sum := by
              simp

/-! ## 5. RankRecordDecomposition への specialisation -/

end CSTMicro

namespace Word

open CSTMicro

namespace RankRecordDecomposition

/--
record decomposition の各 rank block に対応する profile raw cost list。

ここでは full decomposition `startIndex = 0` を使う。
-/
def profileBlockCosts
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : List ℕ :=
  recordProfileBlockCosts H (oddSteps w) h 0 D.lengths

/-- record block 数。 -/
def profileRecordCount
    {w : Word}
    (D : RankRecordDecomposition w 0) : ℕ :=
  D.lengths.length

/-- block-level quotient sum `A_record`。 -/
def profileBlockCostQuotientSum
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockCostQuotientSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCosts H h)

/-- block-level residual sum `R_record`。 -/
def profileBlockResidualCostSum
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  recordBlockResidualCostSum
    (columnLayerGap H (oddSteps w))
    (D.profileBlockCosts H h)

/-- block cost list の長さは record 数そのもの。 -/
theorem profileBlockCosts_length
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) :
    (D.profileBlockCosts H h).length = D.profileRecordCount := by
  unfold profileBlockCosts profileRecordCount
  exact recordProfileBlockCosts_length H (oddSteps w) h 0 D.lengths

/--
record block raw cost の総和は full profile raw cost に exact に一致する。
-/
theorem profileBlockCosts_sum_eq_fullProfileCellCost
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) :
    (D.profileBlockCosts H h).sum =
      columnProfileCellCostSum H (oddSteps w) h := by
  have hLen : D.lengths.sum = oddSteps w := by
    simpa using D.start_add_lengths_sum_eq_terminal
  unfold profileBlockCosts
  rw [recordProfileBlockCosts_sum_eq_interval]
  rw [hLen]
  exact columnProfileCellCostInterval_zero_full H (oddSteps w) h

/--
block-level Euclid decomposition。

  C_total = G * A_record + R_record.
-/
theorem fullProfileCellCost_eq_gap_mul_recordQuotient_add_recordResidual
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) :
    columnProfileCellCostSum H (oddSteps w) h =
      columnLayerGap H (oddSteps w) * D.profileBlockCostQuotientSum H h +
        D.profileBlockResidualCostSum H h := by
  have hList :=
    listCostSum_eq_gap_mul_quotientSum_add_residualSum
      (columnLayerGap H (oddSteps w))
      (D.profileBlockCosts H h)
  rw [D.profileBlockCosts_sum_eq_fullProfileCellCost H h] at hList
  simpa [profileBlockCostQuotientSum, profileBlockResidualCostSum] using hList

/--
4A の第一主結果。

record block residual は cell-level residual 以下。
-/
theorem profileBlockResidualCostSum_le_cellResidualCostSum
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ) :
    D.profileBlockResidualCostSum H h ≤
      columnProfileResidualCostSum H (oddSteps w) h := by
  have hLen : D.lengths.sum = oddSteps w := by
    simpa using D.start_add_lengths_sum_eq_terminal
  have h :=
    recordProfileBlockResidualSum_le_intervalResidual
      H (oddSteps w) h 0 D.lengths
  rw [hLen, columnProfileResidualCostInterval_zero_full] at h
  simpa [profileBlockResidualCostSum, profileBlockCosts] using h

/--
4A の record-count strict bound。

  R_record < G * (#records).
-/
theorem profileBlockResidualCostSum_lt_gap_mul_recordCount
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    D.profileBlockResidualCostSum H h <
      columnLayerGap H (oddSteps w) * D.profileRecordCount := by
  have hLengthsNe : D.lengths ≠ [] := D.lengths_nonempty
  have hCostsNe : D.profileBlockCosts H h ≠ [] := by
    intro hNil
    have hLenEq := D.profileBlockCosts_length H h
    rw [hNil] at hLenEq
    have : D.lengths.length = 0 := by
      simpa [profileRecordCount] using hLenEq.symm
    exact hLengthsNe (List.length_eq_zero_iff.mp this)
  have hStrict :=
    recordBlockResidualCostSum_lt_gap_mul_length
      hGap hCostsNe
  rw [D.profileBlockCosts_length H h] at hStrict
  simpa [profileBlockResidualCostSum] using hStrict

/--
4A の第二主結果。

cell-level と record-block-level の Euclid 分解の差は、
ある `kappa` 個の full gap に exact に吸収される。

  A_record = A(h) + kappa,
  R(h) = G*kappa + R_record.
-/
theorem exists_recordCoarseningCarry
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    ∃ kappa : ℕ,
      D.profileBlockCostQuotientSum H h =
        columnProfileCostQuotientSum H (oddSteps w) h + kappa ∧
      columnProfileResidualCostSum H (oddSteps w) h =
        columnLayerGap H (oddSteps w) * kappa +
          D.profileBlockResidualCostSum H h := by
  let G := columnLayerGap H (oddSteps w)
  let A := columnProfileCostQuotientSum H (oddSteps w) h
  let R := columnProfileResidualCostSum H (oddSteps w) h
  let Arec := D.profileBlockCostQuotientSum H h
  let Rrec := D.profileBlockResidualCostSum H h
  have hCell :=
    columnProfileCellCostSum_eq_gap_mul_quotientSum_add_residualSum
      H (oddSteps w) h
  have hRecord :=
    D.fullProfileCellCost_eq_gap_mul_recordQuotient_add_recordResidual H h
  have hEq : G * A + R = G * Arec + Rrec := by
    dsimp [G, A, R, Arec, Rrec]
    rw [← hCell, ← hRecord]
  have hRle : Rrec ≤ R := by
    dsimp [Rrec, R]
    exact D.profileBlockResidualCostSum_le_cellResidualCostSum H h
  have hAle : A ≤ Arec := by
    by_contra hnot
    have hlt : Arec < A := by omega
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
        G * A + R = G * A + (G * kappa + Rrec) := by
      simpa [Nat.add_assoc] using hEq'
    exact Nat.add_left_cancel hEq''
  refine ⟨kappa, ?_, ?_⟩
  · simpa [Arec, A] using hAeq
  · simpa [R, G, Rrec] using hReq

/--
`kappa` の存在から直ちに得る、block coarsening は residual budget を増やさないという形。
-/
theorem profileBlockResidualCostSum_le_cellResidualCostSum_via_kappa
    {w : Word}
    (D : RankRecordDecomposition w 0)
    (H : ℕ)
    (h : ℕ → ℕ)
    (hGap : 0 < columnLayerGap H (oddSteps w)) :
    D.profileBlockResidualCostSum H h ≤
      columnProfileResidualCostSum H (oddSteps w) h := by
  obtain ⟨kappa, hA, hR⟩ := D.exists_recordCoarseningCarry H h hGap
  rw [hR]
  exact Nat.le_add_left _ _

end RankRecordDecomposition

end Word
end Collatz2
