import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualRecordFerrersDeficit
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge

/-!
# unit-cell Ferrers 表現から maximal horizontal bands への exact coarsening

`actualFerrersBands` は証明に適した canonical 表現として、欠けた各セルを
長さ1の `FerrersRowBand` にしている。
巨大探索では、同じ level で横に連続するセルを一つの帯 `[start,start+length)`
へまとめたい。

このファイルでは

* 一つの連続 horizontal run を unit cells から一帯へまとめても deficit が不変、
* actual unit cells を maximal runs が permutation として被覆すれば、
  全 deficit も exact に不変、

を証明する。

最大 run の「発見アルゴリズム」と、その評価値保存を分離することで、
探索側は run detector を高速実装し、証明側は小さな cover certificate だけを検査できる。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open scoped BigOperators

/-- Ferrers の一セル `(k,level)` の global weight。 -/
def ferrersCellWeight (globalLength k level : ℕ) : ℤ :=
  (2 : ℤ) ^ (Word.criticalHeight k - level) *
    (3 : ℤ) ^ (globalLength - (k + 1))

/-- 開始位置から右へ `length` 個並ぶ unit-cell 帯列。 -/
def horizontalUnitBands
    (start level : ℕ) : ℕ → List FerrersRowBand
  | 0 => []
  | length + 1 =>
      horizontalUnitBands start level length ++
        [({ start := start + length, length := 1, level := level } : FerrersRowBand)]

/-- unit-cell horizontal run の deficit はセル重みの range sum。 -/
theorem integerFerrersDeficit_horizontalUnitBands
    (globalLength start level length : ℕ) :
    integerFerrersDeficit globalLength
        (horizontalUnitBands start level length) =
      Finset.sum (Finset.range length)
        (fun k => ferrersCellWeight globalLength (start + k) level) := by
  induction length with
  | zero =>
      simp [horizontalUnitBands, integerFerrersDeficit]
  | succ length ih =>
      rw [horizontalUnitBands, integerFerrersDeficit_append]
      rw [ih, Finset.sum_range_succ]
      simp [integerFerrersDeficit, rowBandExpandedCellSum_unit,
        ferrersCellWeight]

/-- critical height は index に対して単調非減少。 -/
theorem criticalHeight_mono_of_le
    {a b : ℕ}
    (h : a ≤ b) :
    Word.criticalHeight a ≤ Word.criticalHeight b := by
  by_cases hab : a = b
  · subst b
    exact le_rfl
  · have hlt : a < b := lt_of_le_of_ne h hab
    have hb := beattyIndex_strictMono hlt
    simpa [criticalHeight_eq_beattyIndex] using Nat.le_of_lt hb

/--
一つの長い水平帯の expanded evaluation は、その帯に含まれる unit cells の和。
-/
theorem rowBandExpandedCellSum_eq_cellWeight_sum
    (globalLength start level length : ℕ)
    (hLevel : level ≤ Word.criticalHeight start)
    (hEnd : start + length ≤ globalLength) :
    rowBandExpandedCellSum globalLength
      ({ start := start, length := length, level := level } : FerrersRowBand) =
    Finset.sum (Finset.range length)
      (fun k => ferrersCellWeight globalLength (start + k) level) := by
  unfold rowBandExpandedCellSum
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < length := Finset.mem_range.mp hk
  have hStartLeIndex :
      Word.criticalHeight start ≤ Word.criticalHeight (start + k) :=
    criticalHeight_mono_of_le (Nat.le_add_right start k)
  have hLevelIndex : level ≤ Word.criticalHeight (start + k) :=
    le_trans hLevel hStartLeIndex
  have hTwoExp :
      (Word.criticalHeight start - level) +
          (Word.criticalHeight (start + k) - Word.criticalHeight start) =
        Word.criticalHeight (start + k) - level := by
    omega
  have hThreeExp :
      (globalLength - (start + length)) + (length - (k + 1)) =
        globalLength - ((start + k) + 1) := by
    omega
  unfold ferrersCellWeight
  change
    (2 : ℤ) ^ (Word.criticalHeight start - level) *
        (3 : ℤ) ^ (globalLength - (start + length)) *
        ((2 : ℤ) ^
            (Word.criticalHeight (start + k) -
              Word.criticalHeight start) *
          (3 : ℤ) ^ (length - (k + 1))) =
      (2 : ℤ) ^ (Word.criticalHeight (start + k) - level) *
        (3 : ℤ) ^ (globalLength - ((start + k) + 1))
  calc
    (2 : ℤ) ^ (Word.criticalHeight start - level) *
        (3 : ℤ) ^ (globalLength - (start + length)) *
        ((2 : ℤ) ^
            (Word.criticalHeight (start + k) -
              Word.criticalHeight start) *
          (3 : ℤ) ^ (length - (k + 1)))
        =
      ((2 : ℤ) ^ (Word.criticalHeight start - level) *
        (2 : ℤ) ^
          (Word.criticalHeight (start + k) -
            Word.criticalHeight start)) *
      ((3 : ℤ) ^ (globalLength - (start + length)) *
        (3 : ℤ) ^ (length - (k + 1))) := by
          ring
    _ =
      (2 : ℤ) ^
          ((Word.criticalHeight start - level) +
            (Word.criticalHeight (start + k) -
              Word.criticalHeight start)) *
        (3 : ℤ) ^
          ((globalLength - (start + length)) +
            (length - (k + 1))) := by
          rw [← pow_add, ← pow_add]
    _ =
      (2 : ℤ) ^ (Word.criticalHeight (start + k) - level) *
        (3 : ℤ) ^ (globalLength - ((start + k) + 1)) := by
          rw [hTwoExp, hThreeExp]

/--
横に連続する unit cells は一つの `FerrersRowBand` へ exact に coarsen できる。
-/
theorem horizontalRun_exact_coarsening
    (globalLength start level length : ℕ)
    (hLevel : level ≤ Word.criticalHeight start)
    (hEnd : start + length ≤ globalLength) :
    integerFerrersDeficit globalLength
        (horizontalUnitBands start level length) =
      integerFerrersDeficit globalLength
        [({ start := start, length := length, level := level } : FerrersRowBand)] := by
  rw [integerFerrersDeficit_horizontalUnitBands]
  simp only [integerFerrersDeficit]
  rw [rowBandExpandedCellSum_eq_cellWeight_sum
    globalLength start level length hLevel hEnd]
  simp

/--
actual defect diagram の一つの maximal horizontal run。

`covered` が帯内部、`left_maximal` / `right_maximal` が両端で延長不能なことを表す。
-/
structure MaximalHorizontalRun (w : Word) where
  start : ℕ
  length : ℕ
  level : ℕ
  length_pos : 0 < length
  level_pos : 0 < level
  end_le : start + length ≤ Word.oddSteps w
  covered : ∀ k : ℕ, k < length →
    level ≤ Word.criticalDefect w (start + k)
  left_maximal :
    start = 0 ∨ Word.criticalDefect w (start - 1) < level
  right_maximal :
    start + length = Word.oddSteps w ∨
      Word.criticalDefect w (start + length) < level

/-- maximal run を一つの圧縮帯へ写す。 -/
def MaximalHorizontalRun.toBand
    {w : Word}
    (r : MaximalHorizontalRun w) : FerrersRowBand :=
  { start := r.start, length := r.length, level := r.level }

/-- maximal run の先頭 level は critical roof 以下。 -/
theorem MaximalHorizontalRun.level_le_criticalHeight_start
    {w : Word}
    (r : MaximalHorizontalRun w) :
    r.level ≤ Word.criticalHeight r.start := by
  have hCover0 : r.level ≤ Word.criticalDefect w r.start := by
    simpa using r.covered 0 r.length_pos
  unfold Word.criticalDefect at hCover0
  omega

/-- 一つの maximal run の unit cells と圧縮帯は exact に同じ deficit。 -/
theorem MaximalHorizontalRun.exact_coarsening
    {w : Word}
    (r : MaximalHorizontalRun w) :
    integerFerrersDeficit (Word.oddSteps w)
        (horizontalUnitBands r.start r.level r.length) =
      integerFerrersDeficit (Word.oddSteps w) [r.toBand] := by
  exact horizontalRun_exact_coarsening
    (Word.oddSteps w) r.start r.level r.length
    r.level_le_criticalHeight_start r.end_le

/-- `integerFerrersDeficit` は list permutation に依存しない。 -/
theorem integerFerrersDeficit_perm
    (globalLength : ℕ)
    {xs ys : List FerrersRowBand}
    (h : xs.Perm ys) :
    integerFerrersDeficit globalLength xs =
      integerFerrersDeficit globalLength ys := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp [integerFerrersDeficit, ih]
  | swap a b l =>
      simp [integerFerrersDeficit, add_comm, add_left_comm, add_assoc]
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- maximal runs を unit cells へ展開する。 -/
def maximalRunsUnitBands
    {w : Word} : List (MaximalHorizontalRun w) → List FerrersRowBand
  | [] => []
  | r :: rs =>
      horizontalUnitBands r.start r.level r.length ++ maximalRunsUnitBands rs

/-- maximal runs を一帯ずつの圧縮表現へする。 -/
def maximalRunsBands
    {w : Word} : List (MaximalHorizontalRun w) → List FerrersRowBand
  | [] => []
  | r :: rs => r.toBand :: maximalRunsBands rs

/-- run list 全体でも unit 展開と圧縮表現の deficit は exact に一致する。 -/
theorem maximalRuns_exact_coarsening
    {w : Word}
    (runs : List (MaximalHorizontalRun w)) :
    integerFerrersDeficit (Word.oddSteps w) (maximalRunsUnitBands runs) =
      integerFerrersDeficit (Word.oddSteps w) (maximalRunsBands runs) := by
  induction runs with
  | nil => rfl
  | cons r rs ih =>
      rw [maximalRunsUnitBands, integerFerrersDeficit_append]
      rw [r.exact_coarsening]
      simp only [maximalRunsBands, integerFerrersDeficit]
      rw [ih]
      ring

/--
actual unit cells を maximal horizontal runs が重複なく被覆したことを表す certificate。
順序は column-major / row-major で異なってよいので `Perm` で保持する。
-/
structure MaximalHorizontalBandCover (w : Word) where
  runs : List (MaximalHorizontalRun w)
  unit_perm :
    List.Perm
      (maximalRunsUnitBands runs)
      (actualFerrersBands w)

/-- cover certificate が指定する最終 maximal horizontal band 列。 -/
def maximalHorizontalBands
    {w : Word}
    (C : MaximalHorizontalBandCover w) : List FerrersRowBand :=
  maximalRunsBands C.runs

/--
actual unit-cell representation から maximal horizontal bands への exact coarsening。
これが巨大探索で使う representation transport である。
-/
theorem actualFerrersBands_eq_maximalHorizontalBands_deficit
    {w : Word}
    (C : MaximalHorizontalBandCover w) :
    integerFerrersDeficit (Word.oddSteps w) (actualFerrersBands w) =
      integerFerrersDeficit (Word.oddSteps w) (maximalHorizontalBands C) := by
  calc
    integerFerrersDeficit (Word.oddSteps w) (actualFerrersBands w)
        = integerFerrersDeficit (Word.oddSteps w)
            (maximalRunsUnitBands C.runs) := by
              symm
              exact integerFerrersDeficit_perm (Word.oddSteps w) C.unit_perm
    _ = integerFerrersDeficit (Word.oddSteps w)
          (maximalRunsBands C.runs) := maximalRuns_exact_coarsening C.runs
    _ = integerFerrersDeficit (Word.oddSteps w)
          (maximalHorizontalBands C) := rfl

/-- maximal horizontal bands は同じ shifted-Phi deficit も保持する。 -/
theorem actualFerrersBands_eq_maximalHorizontalBands_phi
    {w : Word}
    (C : MaximalHorizontalBandCover w) :
    rowBandPhiSum (Word.oddSteps w) (actualFerrersBands w) =
      rowBandPhiSum (Word.oddSteps w) (maximalHorizontalBands C) := by
  rw [← integerFerrersDeficit_eq_rowBandPhiSum,
      ← integerFerrersDeficit_eq_rowBandPhiSum]
  exact actualFerrersBands_eq_maximalHorizontalBands_deficit C

end DoubleDecomposition
end CSTMicro
end Collatz2
