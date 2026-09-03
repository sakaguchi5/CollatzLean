import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# RecordFerrers 横帯と shifted Phi の評価

同じ区間に二種類の分解を重ねる。

* Record/Ferrers 側: どの横帯を置くかを決める「構成用分解」。
* Christoffel/Ostrowski 側: その横帯の重みを `Phi` で計算する「計算用分解」。

両者の block 境界を同一視しない。ここで一致させるのは、同じ区間に対する
整数評価値だけである。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open scoped BigOperators

/--
開始位置 `a`、長さ `len` の shifted critical interval に対する整数 `Phi`。
高さは区間先頭からの相対高さで正規化する。
-/
def criticalIntervalPhiZ (a len : ℕ) : ℤ :=
  Finset.sum (Finset.range len) (fun k =>
    (2 : ℤ) ^ (Word.criticalHeight (a + k) - Word.criticalHeight a) *
      (3 : ℤ) ^ (len - (k + 1)))

/-- Record/Ferrers の一つの水平帯。 -/
structure FerrersRowBand where
  start : ℕ
  length : ℕ
  level : ℕ

/--
一つの水平帯をセルごとに展開した整数重み。
`globalLength` は全区間の長さであり、帯自身の長さとは独立。
-/
def rowBandExpandedCellSum
    (globalLength : ℕ)
    (b : FerrersRowBand) : ℤ :=
  Finset.sum (Finset.range b.length) (fun k =>
    ((2 : ℤ) ^ (Word.criticalHeight b.start - b.level) *
      (3 : ℤ) ^ (globalLength - (b.start + b.length))) *
      ((2 : ℤ) ^
          (Word.criticalHeight (b.start + k) - Word.criticalHeight b.start) *
        (3 : ℤ) ^ (b.length - (k + 1))))

/-- 同じ水平帯を shifted `Phi` 一個で評価した重み。 -/
def rowBandPhiWeight
    (globalLength : ℕ)
    (b : FerrersRowBand) : ℤ :=
  (2 : ℤ) ^ (Word.criticalHeight b.start - b.level) *
    (3 : ℤ) ^ (globalLength - (b.start + b.length)) *
      criticalIntervalPhiZ b.start b.length

/-- セル展開と shifted `Phi` 評価は exact に一致する。 -/
theorem rowBandExpandedCellSum_eq_rowBandPhiWeight
    (globalLength : ℕ)
    (b : FerrersRowBand) :
    rowBandExpandedCellSum globalLength b =
      rowBandPhiWeight globalLength b := by
  unfold rowBandExpandedCellSum rowBandPhiWeight criticalIntervalPhiZ
  rw [← Finset.mul_sum]

/-- Record 分解で指定された複数横帯のセル評価。 -/
def integerFerrersDeficit
    (globalLength : ℕ) : List FerrersRowBand → ℤ
  | [] => 0
  | b :: bs =>
      rowBandExpandedCellSum globalLength b +
        integerFerrersDeficit globalLength bs

/-- 同じ Record 横帯列を、各 shifted `Phi` で評価した総和。 -/
def rowBandPhiSum
    (globalLength : ℕ) : List FerrersRowBand → ℤ
  | [] => 0
  | b :: bs =>
      rowBandPhiWeight globalLength b +
        rowBandPhiSum globalLength bs

/--
Record/Ferrers の integer deficit は、各横帯の shifted `Phi` 評価の総和に等しい。

重要なのは「Record block = Ostrowski block」ではない点である。
Record が作った帯 `[a,b)` ごとに、計算側がその同一区間の `Phi[a,b]` を返す。
-/
theorem integerFerrersDeficit_eq_rowBandPhiSum
    (globalLength : ℕ)
    (bands : List FerrersRowBand) :
    integerFerrersDeficit globalLength bands =
      rowBandPhiSum globalLength bands := by
  induction bands with
  | nil => rfl
  | cons b bs ih =>
      simp only [integerFerrersDeficit, rowBandPhiSum]
      rw [rowBandExpandedCellSum_eq_rowBandPhiWeight, ih]

end DoubleDecomposition
end CSTMicro
end Collatz2
