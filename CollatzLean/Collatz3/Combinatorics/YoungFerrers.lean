import Mathlib.Data.Fintype.BigOperators

/-!
# Collatz3: Young / Ferrers の純粋な有限組合せ層

このファイルには Collatz 固有の定義を入れない。

重要な設計上の区別は次の二つ。

* `OrderedColumnDiagram m` は、列の順序を保持した有限列図形 `Fin m → ℕ`。
* `FerrersShape m` は、その列高が antitone である古典的 Ferrers / Young 型の図形。

Collatz の critical profile は列順序そのものに意味があり、一般には列高が単調とは限らない。
したがって profile を最初から古典 Ferrers 図形と同一視せず、まず ordered diagram として保持する。
古典 Ferrers 条件が成立する場合だけ `IsFerrers` を介して `FerrersShape` に上げる。
-/

namespace Collatz3
namespace Combinatorics

open scoped BigOperators

/--
`m` 本の列からなる順序付き有限列図形。
列 `k` の高さを自然数で持つだけで、横方向の単調性は仮定しない。
-/
abbrev OrderedColumnDiagram (m : ℕ) := Fin m → ℕ

/-- 列 `k` の高さ `D k` より下にある cell。 -/
def HasCell
    {m : ℕ}
    (D : OrderedColumnDiagram m)
    (k : Fin m)
    (r : ℕ) : Prop :=
  r < D k

/--
有限列図形の cell 数。
各列高の総和として定義し、cell 集合そのものは primitive にしない。
-/
def cellCount
    {m : ℕ}
    (D : OrderedColumnDiagram m) : ℕ :=
  ∑ k : Fin m, D k

/-- 同じ列では、上の cell が存在すればそれより下の cell も存在する。 -/
theorem HasCell.downward
    {m : ℕ}
    {D : OrderedColumnDiagram m}
    {k : Fin m}
    {r s : ℕ}
    (hrs : r ≤ s)
    (hs : HasCell D k s) :
    HasCell D k r := by
  unfold HasCell at hs ⊢
  omega

/--
古典 Ferrers 条件。
列番号が右へ進むほど列高が増えないことだけを要求する。
-/
def IsFerrers
    {m : ℕ}
    (D : OrderedColumnDiagram m) : Prop :=
  Antitone D

/--
古典 Ferrers / Young 型の有限図形。
本体は ordered diagram と Ferrers 条件の subtype にとどめる。
-/
abbrev FerrersShape (m : ℕ) :=
  {D : OrderedColumnDiagram m // IsFerrers D}

/-- Young 図形として読む場合の同義名。向きの流儀だけを変え、データは増やさない。 -/
abbrev YoungShape (m : ℕ) := FerrersShape m

namespace FerrersShape

/-- Ferrers shape の underlying ordered diagram。 -/
def diagram
    {m : ℕ}
    (F : FerrersShape m) : OrderedColumnDiagram m :=
  F.1

/-- Ferrers shape の列高は antitone。 -/
theorem antitone
    {m : ℕ}
    (F : FerrersShape m) :
    Antitone F.1 :=
  F.2

/-- Ferrers shape の cell 数は underlying diagram の cell 数。 -/
def cellCount
    {m : ℕ}
    (F : FerrersShape m) : ℕ :=
  Combinatorics.cellCount F.1

end FerrersShape

end Combinatorics
end Collatz3
