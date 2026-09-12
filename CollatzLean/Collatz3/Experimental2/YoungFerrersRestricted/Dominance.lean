import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Durfee

/-!
# Collatz3 Experimental2: column dominance と RecordFerrers 比較

現在の `FerrersShape` は列高表示なので、このファイルでは
各 prefix に含まれる cell 数を比較する column-dominance を採用する。

`A` が `B` を column-dominate するとは、任意の先頭 `k` 列について
`B` の cell 数が `A` 以下であることとする。

RecordFerrers では全 code の横幅が同じ `m-1` なので、
dominance は直ちに Young 面積の大小を与える。
後段で actual Collatz correction がこの順序の一方向へしか動かないことを示せれば、
pure mechanical shape と actual shape の比較不変量として使える。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 最初の `k` 列に含まれる cell 数。 -/
def prefixColumnMass
    (c : WidthDropCode)
    (k : ℕ) : ℕ :=
  ((columnListFromWidthDropCode c).take k).sum

/--
列表示における dominance。
`A` が `B` を dominate するなら、全 prefix で `B ≤ A`。
-/
def ColumnDominates
    (A B : WidthDropCode) : Prop :=
  ∀ k : ℕ, prefixColumnMass B k ≤ prefixColumnMass A k

/-- column dominance は反射的。 -/
theorem columnDominates_refl
    (A : WidthDropCode) :
    ColumnDominates A A := by
  intro k
  exact Nat.le_refl _

/-- column dominance は推移的。 -/
theorem columnDominates_trans
    {A B C : WidthDropCode}
    (hAB : ColumnDominates A B)
    (hBC : ColumnDominates B C) :
    ColumnDominates A C := by
  intro k
  exact le_trans (hBC k) (hAB k)

/-- 全横幅まで取った prefix mass は code area に一致する。 -/
theorem prefixColumnMass_full
    (c : WidthDropCode) :
    prefixColumnMass c (codeWidth c) = codeArea c := by
  unfold prefixColumnMass
  rw [← columnListFromWidthDropCode_length c]
  simp [columnListFromWidthDropCode_sum]

/--
同じ横幅の二図形では、column dominance は全 cell 数の大小を与える。
-/
theorem codeArea_le_of_columnDominates
    {A B : WidthDropCode}
    (hWidth : codeWidth A = codeWidth B)
    (hDom : ColumnDominates A B) :
    codeArea B ≤ codeArea A := by
  have h := hDom (codeWidth B)
  rw [prefixColumnMass_full] at h
  have hWidth' : codeWidth B = codeWidth A := hWidth.symm
  rw [hWidth', prefixColumnMass_full] at h
  exact h

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- 二つの完成 RecordFerrers の rank-envelope shape を column dominance で比較する。 -/
def RankColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) : Prop :=
  ColumnDominates R.plateauWidthDropCode S.plateauWidthDropCode

/-- RecordFerrers dominance は反射的。 -/
theorem rankColumnDominates_refl
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    RankColumnDominates R R :=
  columnDominates_refl R.plateauWidthDropCode

/-- RecordFerrers dominance は推移的。 -/
theorem rankColumnDominates_trans
    {β : ℕ → ℕ}
    {m : ℕ}
    {R S T : RecordFerrers β m}
    (hRS : RankColumnDominates R S)
    (hST : RankColumnDominates S T) :
    RankColumnDominates R T :=
  columnDominates_trans hRS hST

/--
同じ `β,m` の RecordFerrers では横幅が共通 `m-1` なので、
dominance から Young cell count の大小が従う。
-/
theorem youngCellCount_le_of_rankColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    {R S : RecordFerrers β m}
    (hDom : RankColumnDominates R S) :
    S.youngCellCount ≤ R.youngCellCount := by
  unfold youngCellCount
  apply codeArea_le_of_columnDominates
  · rw [R.plateauCode_width, S.plateauCode_width]
  · exact hDom

/-- dominance 仮定から任意 prefix の cell 不等式を直接取り出す。 -/
theorem prefixColumnMass_le_of_rankColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    {R S : RecordFerrers β m}
    (hDom : RankColumnDominates R S)
    (k : ℕ) :
    prefixColumnMass S.plateauWidthDropCode k ≤
      prefixColumnMass R.plateauWidthDropCode k :=
  hDom k

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
