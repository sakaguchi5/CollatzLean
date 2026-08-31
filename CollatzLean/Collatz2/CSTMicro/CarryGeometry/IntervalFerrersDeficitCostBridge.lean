import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RecordFerrersGenericStartCoarsening
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ProfileCostClosedForm
import CollatzLean.Collatz2.Geometry.IntegerFerrersDeficit

/-!
# Interval Ferrers deficit -- cell cost exact bridge

rank interval `[a,a+n)` に対して integer Ferrers deficit

  F_int(w,a,n)
    = sum_{t<n} integerFerrersDeficitTerm(w,a+t)

を定義する。

`ColumnLayerCostDynamics` の一 cell exact identity は

  3^m C(k,j)
    = G*T(k,j) + columnLayerScaledPowerTerm(m,k,j)

である。

これを interval 内の全 cell に足すと

  3^m C_int
    = G*T_int + dyadicCellInterval

となる。

さらに FirstCrossing word の actual extra-depth profileについて、
一 column の dyadic sumは

  (2^criticalHeight(k) - 2^prefixTwoDepth(k))
    * 3^(m-k-1)

へ閉じ、これは `integerFerrersDeficitTerm` そのものになる。

したがって

  3^m C_int = G*T_int + F_int

を exact に得る。

注意:
現 repo の `columnLayerCellCost_scaled_exact` は actual `FerrersStep` と
その step の current depth を入力に取る局所定理である。
final profile の全 cell を actual chain の各 step へ一括再索引する theorem はまだない。
そこで本ファイルでは、その局所 exact equation が interval 全 cell に供給されていることを
`ColumnLayerScaledExactIntervalWitness` として明示する。
この witness を actual critical-boundary chain から canonical に構成することは、
次段の独立した realization bridge として残す。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

/-! ## 1. interval Ferrers deficit -/

/--
integer Ferrers deficit の rank interval `[a,a+n)` 版。
-/
def integerFerrersDeficitInterval
    (w : Word)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t => integerFerrersDeficitTerm w (a + t))

/-- interval deficit は隣接 interval に対して exact additive。 -/
theorem integerFerrersDeficitInterval_add
    (w : Word)
    (a r s : ℕ) :
    integerFerrersDeficitInterval w a (r + s) =
      integerFerrersDeficitInterval w a r +
        integerFerrersDeficitInterval w (a + r) s := by
  unfold integerFerrersDeficitInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.add_assoc]

/--
dyadic cell term の rank interval 二重和。
-/
def profileDyadicCellInterval
    (m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) : ℕ :=
  Finset.sum (Finset.range n)
    (fun t =>
      Finset.sum (Finset.range (h (a + t)))
        (fun j => profileDyadicCellTerm m (a + t) j))

/--
一つの FirstCrossing column で、integer Ferrers deficit term は
extra-depth column の closed dyadic term と exact に一致する。
-/
theorem integerFerrersDeficitTerm_eq_profileDyadicClosedColumn
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    integerFerrersDeficitTerm w k =
      profileDyadicClosedColumn
        (oddSteps w) k (extraDepth w k) := by
  have hPrefixLe :
      prefixTwoDepth w k ≤ Word.criticalHeight k := by
    by_cases hk0 : k = 0
    · subst k
      simp [prefixTwoDepth, Word.criticalHeight]
    · exact
        hF.prefixTwoDepth_le_criticalHeight
          (Nat.pos_of_ne_zero hk0) hkLt
  have hDepth :
      Word.criticalHeight k - extraDepth w k =
        prefixTwoDepth w k := by
    unfold extraDepth
    omega
  unfold integerFerrersDeficitTerm
    criticalAffineTerm
    affinePathTerm
    profileDyadicClosedColumn
  rw [beattyIndex_eq_wordCriticalHeight_all]
  rw [hDepth]
  rw [Nat.sub_mul]

/--
FirstCrossing の actual extra-depth profile では、
interval の dyadic cell 二重和は integer Ferrers deficit interval そのもの。
-/
theorem profileDyadicCellInterval_eq_integerFerrersDeficitInterval
    {w : Word}
    (hF : FirstCrossing w)
    {a n : ℕ}
    (hRange : a + n ≤ oddSteps w) :
    profileDyadicCellInterval
        (oddSteps w) (extraDepth w) a n =
      integerFerrersDeficitInterval w a n := by
  unfold profileDyadicCellInterval integerFerrersDeficitInterval
  apply Finset.sum_congr rfl
  intro t ht
  have htLt : t < n :=
    Finset.mem_range.mp ht
  have hkLt : a + t < oddSteps w := by
    omega
  have hDepthLe :
      extraDepth w (a + t) ≤ beattyIndex (a + t) := by
    unfold extraDepth
    rw [beattyIndex_eq_wordCriticalHeight_all]
    exact Nat.sub_le _ _
  calc
    Finset.sum (Finset.range (extraDepth w (a + t)))
        (fun j =>
          profileDyadicCellTerm (oddSteps w) (a + t) j)
        =
      profileDyadicClosedColumn
        (oddSteps w) (a + t) (extraDepth w (a + t)) := by
          exact profileDyadicColumnSum_eq_closed hDepthLe
    _ = integerFerrersDeficitTerm w (a + t) := by
          symm
          exact
            integerFerrersDeficitTerm_eq_profileDyadicClosedColumn
              hF hkLt

/-! ## 2. interval 全 cell の local exact witness -/

/--
interval `[a,a+n)` の各 occupied cell に対する
`columnLayerCellCost_scaled_exact` 型の exact equation をまとめた packet。

`quotient t j` が局所 theorem の existential witness `T` に対応する。
-/
structure ColumnLayerScaledExactIntervalWitness
    (H m : ℕ)
    (h : ℕ → ℕ)
    (a n : ℕ) where
  quotient : ℕ → ℕ → ℤ
  exact_cell :
    ∀ t j : ℕ,
      t < n →
      j < h (a + t) →
      (3 : ℤ) ^ m *
          (columnLayerCellCostNat
            H m (a + t) j : ℤ) =
        (columnLayerGap H m : ℤ) * quotient t j +
          columnLayerScaledPowerTerm m (a + t) j

namespace ColumnLayerScaledExactIntervalWitness

/-- interval 全 cell の local quotient witness の総和。 -/
def scaledQuotientSum
    {H m : ℕ}
    {h : ℕ → ℕ}
    {a n : ℕ}
    (W : ColumnLayerScaledExactIntervalWitness H m h a n) : ℤ :=
  Finset.sum (Finset.range n)
    (fun t =>
      Finset.sum (Finset.range (h (a + t)))
        (fun j => W.quotient t j))

/--
一 column 内で local scaled exact equations を足し上げる。
-/
private theorem scaled_column_exact
    {H m : ℕ}
    {h : ℕ → ℕ}
    {a n : ℕ}
    (W : ColumnLayerScaledExactIntervalWitness H m h a n)
    {t : ℕ}
    (ht : t < n) :
    (3 : ℤ) ^ m *
        (columnProfileCellCostColumn H m h (a + t) : ℤ) =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.range (h (a + t)))
            (fun j => W.quotient t j) +
        (Finset.sum (Finset.range (h (a + t)))
          (fun j => profileDyadicCellTerm m (a + t) j) : ℕ) := by
  unfold columnProfileCellCostColumn
  push_cast
  rw [Finset.mul_sum]
  calc
    Finset.sum (Finset.range (h (a + t)))
        (fun j =>
          (3 : ℤ) ^ m *
            (columnLayerCellCostNat H m (a + t) j : ℤ))
        =
      Finset.sum (Finset.range (h (a + t)))
        (fun j =>
          (columnLayerGap H m : ℤ) * W.quotient t j +
            (profileDyadicCellTerm m (a + t) j : ℤ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hCell :=
            W.exact_cell t j ht (Finset.mem_range.mp hj)
          rw [columnLayerScaledPowerTerm_eq_profileDyadicCellTerm_cast] at hCell
          exact hCell
    _ =
      Finset.sum (Finset.range (h (a + t)))
          (fun j =>
            (columnLayerGap H m : ℤ) * W.quotient t j) +
        Finset.sum (Finset.range (h (a + t)))
          (fun j => (profileDyadicCellTerm m (a + t) j : ℤ)) := by
            exact Finset.sum_add_distrib
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.range (h (a + t)))
            (fun j => W.quotient t j) +
        Finset.sum (Finset.range (h (a + t)))
          (fun j => (profileDyadicCellTerm m (a + t) j : ℤ)) := by
            rw [Finset.mul_sum]

/--
interval 全 cell に local exact equation を足した exact identity。

  3^m C_int = G*T_int + dyadicCellInterval.
-/
theorem columnProfileCellCostInterval_scaled_exact
    {H m : ℕ}
    {h : ℕ → ℕ}
    {a n : ℕ}
    (W : ColumnLayerScaledExactIntervalWitness H m h a n) :
    (3 : ℤ) ^ m *
        (columnProfileCellCostInterval H m h a n : ℤ) =
      (columnLayerGap H m : ℤ) * W.scaledQuotientSum +
        (profileDyadicCellInterval m h a n : ℤ) := by
  unfold columnProfileCellCostInterval
    scaledQuotientSum
    profileDyadicCellInterval
  push_cast
  rw [Finset.mul_sum]
  calc
    Finset.sum (Finset.range n)
        (fun t =>
          (3 : ℤ) ^ m *
            (columnProfileCellCostColumn H m h (a + t) : ℤ))
        =
      Finset.sum (Finset.range n)
        (fun t =>
          (columnLayerGap H m : ℤ) *
              Finset.sum (Finset.range (h (a + t)))
                (fun j => W.quotient t j) +
            Finset.sum (Finset.range (h (a + t)))
              (fun j => (profileDyadicCellTerm m (a + t) j : ℤ))) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hExact :=
            W.scaled_column_exact (Finset.mem_range.mp ht)
          push_cast at hExact
          exact hExact
    _ =
      Finset.sum (Finset.range n)
          (fun t =>
            (columnLayerGap H m : ℤ) *
              Finset.sum (Finset.range (h (a + t)))
                (fun j => W.quotient t j)) +
        Finset.sum (Finset.range n)
          (fun t =>
            Finset.sum (Finset.range (h (a + t)))
              (fun j => (profileDyadicCellTerm m (a + t) j : ℤ))) := by
            exact Finset.sum_add_distrib
    _ =
      (columnLayerGap H m : ℤ) *
          Finset.sum (Finset.range n)
            (fun t =>
              Finset.sum (Finset.range (h (a + t)))
                (fun j => W.quotient t j)) +
        Finset.sum (Finset.range n)
          (fun t =>
            Finset.sum (Finset.range (h (a + t)))
              (fun j => (profileDyadicCellTerm m (a + t) j : ℤ))) := by
            rw [Finset.mul_sum]

end ColumnLayerScaledExactIntervalWitness

/-! ## 3. Ferrers deficit -- cost bridge -/

/--
最重要 bridge。

FirstCrossing word `w` の actual extra-depth profileについて、
interval 全 cell に local scaled exact witnesses があれば

  3^m C_int = G*T + F_int

が exact に成立する。

ここで

* `m = oddSteps w`,
* `H = twoSteps w`,
* `C_int` は `[a,a+n)` の profile raw cell cost,
* `G = 2^H - 3^m`,
* `F_int` は interval integer Ferrers deficit。
-/
theorem intervalFerrersDeficit_cost_scaled_exact
    {w : Word}
    (hF : FirstCrossing w)
    {a n : ℕ}
    (hRange : a + n ≤ oddSteps w)
    (W :
      ColumnLayerScaledExactIntervalWitness
        (twoSteps w)
        (oddSteps w)
        (extraDepth w)
        a n) :
    ∃ T : ℤ,
      (3 : ℤ) ^ oddSteps w *
          (columnProfileCellCostInterval
            (twoSteps w)
            (oddSteps w)
            (extraDepth w)
            a n : ℤ) =
        (columnLayerGap (twoSteps w) (oddSteps w) : ℤ) * T +
          (integerFerrersDeficitInterval w a n : ℤ) := by
  refine ⟨W.scaledQuotientSum, ?_⟩
  have hScaled :=
    W.columnProfileCellCostInterval_scaled_exact
  have hDefNat :=
    profileDyadicCellInterval_eq_integerFerrersDeficitInterval
      hF hRange
  have hDefZ :=
    congrArg (fun x : ℕ => (x : ℤ)) hDefNat
  rw [hDefZ] at hScaled
  exact hScaled

end CSTMicro
end Collatz2
