import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.GenuineDurfee
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Dominance

/-!
# Collatz3 Experimental2: ColumnDominates と classical partition dominance

古典的な partition dominance は、非増加な part 列 `λ, μ` に対し

  μ₀+...+μ_{k-1} ≤ λ₀+...+λ_{k-1}

を全 `k` で要求する。

この repo の Ferrers shape は「列高」を part 列として保存するため、
既存 `ColumnDominates` はまさにその column partition に対する classical dominance である。

一方、通常の row-length convention は Young 共役を取った column partition なので、
row dominance は conjugate code 上の同じ classical dominance として exact に表せる。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 任意の自然数 part 列に対する classical dominance。 -/
def ClassicalDominatesList
    (lambda mu : List ℕ) : Prop :=
  ∀ k : ℕ,
    (mu.take k).sum ≤ (lambda.take k).sum

/-- classical dominance は反射的。 -/
theorem classicalDominatesList_refl
    (lambda : List ℕ) :
    ClassicalDominatesList lambda lambda := by
  intro k
  exact Nat.le_refl _

/-- classical dominance は推移的。 -/
theorem classicalDominatesList_trans
    {lambda mu nu : List ℕ}
    (hLM : ClassicalDominatesList lambda mu)
    (hMN : ClassicalDominatesList mu nu) :
    ClassicalDominatesList lambda nu := by
  intro k
  exact le_trans (hMN k) (hLM k)

/-- width-drop code が表す column partition。 -/
def columnPartitionOfCode
    (c : WidthDropCode) : List ℕ :=
  columnListFromWidthDropCode c

/-- genuine Young 共役が表す row partition。 -/
def rowPartitionOfCode
    (c : WidthDropCode) : List ℕ :=
  columnListFromWidthDropCode (conjugateWidthDropCode c)

/--
C の第一の exact relation：`ColumnDominates` は column-height partition 上の
classical dominance そのもの。
-/
theorem columnDominates_iff_classicalDominates_columnPartition
    (A B : WidthDropCode) :
    ColumnDominates A B ↔
      ClassicalDominatesList
        (columnPartitionOfCode A)
        (columnPartitionOfCode B) := by
  rfl

/-- row convention の classical dominance。 -/
def RowClassicalDominates
    (A B : WidthDropCode) : Prop :=
  ClassicalDominatesList
    (rowPartitionOfCode A)
    (rowPartitionOfCode B)

/--
C の第二の exact relation：row dominance は genuine conjugate code 上の
`ColumnDominates` と exact に一致する。
-/
theorem rowClassicalDominates_iff_conjugateColumnDominates
    (A B : WidthDropCode) :
    RowClassicalDominates A B ↔
      ColumnDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) := by
  rfl

/--
column convention と row convention は Young 共役を一回挟むだけで相互変換できる。
-/
theorem columnDominates_conjugate_iff_rowClassicalDominates
    (A B : WidthDropCode) :
    ColumnDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) ↔
      RowClassicalDominates A B := by
  exact (rowClassicalDominates_iff_conjugateColumnDominates A B).symm

/-- 共役を二回取れば row convention から元の column convention に戻る。 -/
theorem rowClassicalDominates_conjugate_iff_columnDominates
    (A B : WidthDropCode) :
    RowClassicalDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) ↔
      ColumnDominates A B := by
  rw [rowClassicalDominates_iff_conjugateColumnDominates]
  simp

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers の column partition に対する classical dominance。 -/
def RankClassicalColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) : Prop :=
  ClassicalDominatesList
    (columnPartitionOfCode R.plateauWidthDropCode)
    (columnPartitionOfCode S.plateauWidthDropCode)

/-- 既存 `RankColumnDominates` は classical column dominance と exact に同じ。 -/
theorem rankColumnDominates_iff_classical
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) :
    RankColumnDominates R S ↔
      RankClassicalColumnDominates R S := by
  rfl

/-- RecordFerrers の row-length convention に対する classical dominance。 -/
def RankClassicalRowDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) : Prop :=
  RowClassicalDominates R.plateauWidthDropCode S.plateauWidthDropCode

/-- row dominance は共役 plateau code 上の column dominance と exact に一致する。 -/
theorem rankClassicalRowDominates_iff_conjugateColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) :
    RankClassicalRowDominates R S ↔
      ColumnDominates R.conjugatePlateauCode S.conjugatePlateauCode := by
  rfl

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
