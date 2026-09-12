import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Conjugate

import Mathlib.Tactic.Ring

/-!

# Collatz3 Experimental2: Young/Ferrers 面積の cumulative-width 公式

width-drop code `[(r_0,d_0),...,(r_s,d_s)]`
が表す列高は、block `i` で suffix drop `d_i + ... + d_s` に等しい。
従って cell 数は
`Σ r_i * (d_i + ... + d_s)`
であり、和の順序を交換すると `Σ (r_0 + ... + r_i) * d_i` になる。

ここで `r_0 + ... + r_i` は、block `i` の右端までに累積した横幅である。

RecordFerrers では `r_i` が canonical record length、`d_i` が rank drop なので、
一般 Young 面積がそのまま cumulative rank-defect の算術量へ変換される。

-/

namespace Collatz3

namespace Experimental2

namespace YoungFerrersRestricted

/-- width-drop code が展開する実際の列高 list。 -/
def columnListFromWidthDropCode : WidthDropCode → List ℕ
  | [] => []
  | (r, d) :: cs =>
      repeatValue r (d + codeDropSum cs) ++
        columnListFromWidthDropCode cs

/-- 展開した列数は code の全横幅に等しい。 -/
theorem columnListFromWidthDropCode_length :
    ∀ c : WidthDropCode,
      (columnListFromWidthDropCode c).length = codeWidth c
  | [] => by
      simp [columnListFromWidthDropCode, codeWidth, widthsOfCode]
  | (r, d) :: cs => by
      simp [
        columnListFromWidthDropCode,
        codeWidth,
        widthsOfCode,
        columnListFromWidthDropCode_length cs
      ]

/-- plateau code の cell 数。 -/
def codeArea : WidthDropCode → ℕ
  | [] => 0
  | (r, d) :: cs =>
      r * (d + codeDropSum cs) + codeArea cs

/-- 展開した列高の総和は `codeArea` と exact に一致する。 -/
theorem columnListFromWidthDropCode_sum :
    ∀ c : WidthDropCode,
      (columnListFromWidthDropCode c).sum = codeArea c
  | [] => by
      rfl
  | (r, d) :: cs => by
      simp [
        columnListFromWidthDropCode,
        codeArea,
        columnListFromWidthDropCode_sum cs
      ]

/--
左から既に `leftWidth` 列進んだ状態で、
各 drop にその block 右端までの累積横幅を掛けて足す。
-/
def leftWidthWeightedDropSumFrom : ℕ → WidthDropCode → ℕ
  | _leftWidth, [] => 0
  | leftWidth, (r, d) :: cs =>
      (leftWidth + r) * d +
        leftWidthWeightedDropSumFrom (leftWidth + r) cs

/-- 左端、すなわち既通過横幅 `0` から始める weighted-drop sum。 -/
def leftWidthWeightedDropSum (c : WidthDropCode) : ℕ :=
  leftWidthWeightedDropSumFrom 0 c

/--
一般化した和交換公式。

既に左側で通過した `leftWidth` の寄与は
`leftWidth * totalDrop` だけ追加される。
-/
theorem leftWidthWeightedDropSumFrom_eq_area_add
    (leftWidth : ℕ) :
    ∀ c : WidthDropCode,
      leftWidthWeightedDropSumFrom leftWidth c =
        codeArea c + leftWidth * codeDropSum c
  | [] => by
      simp [
        leftWidthWeightedDropSumFrom,
        codeArea,
        codeDropSum,
        dropsOfCode
      ]
  | (r, d) :: cs => by
      rw [leftWidthWeightedDropSumFrom]
      rw [
        leftWidthWeightedDropSumFrom_eq_area_add
          (leftWidth + r) cs
      ]
      simp [codeArea, codeDropSum, dropsOfCode]
      ring

/--
Young/Ferrers cell count の block 公式：

`suffix-height × width` と
`cumulative-width × drop` は exact に同じ。
-/
theorem codeArea_eq_leftWidthWeightedDropSum
    (c : WidthDropCode) :
    codeArea c = leftWidthWeightedDropSum c := by
  unfold leftWidthWeightedDropSum
  have h := leftWidthWeightedDropSumFrom_eq_area_add 0 c
  simpa using h.symm

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers rank-envelope Young 図形の cell 数を plateau code から読む。 -/
def youngCellCount
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : ℕ :=
  codeArea R.plateauWidthDropCode

/-- cell 数は actual plateau column list の総和。 -/
theorem youngCellCount_eq_column_sum
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.youngCellCount =
      (columnListFromWidthDropCode R.plateauWidthDropCode).sum := by
  rw [youngCellCount]
  exact
    (columnListFromWidthDropCode_sum R.plateauWidthDropCode).symm

/--
RecordFerrers の Young 面積は
cumulative width × rank drop の和に等しい。
-/
theorem youngCellCount_eq_leftWidthWeightedRankDrop
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.youngCellCount =
      leftWidthWeightedDropSum R.plateauWidthDropCode := by
  exact
    codeArea_eq_leftWidthWeightedDropSum R.plateauWidthDropCode

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
