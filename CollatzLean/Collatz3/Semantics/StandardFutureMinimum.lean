import CollatzLean.Collatz3.Semantics.FutureMinimum

/-!
# Collatz3: standard future-minimum property

単なる future-minimum 部分列と、各 current の直後の tail 全体から最小値を選ぶ
**標準列**を分離する。

stable core では無限 selector を classical に構成しない。
局所正本は `NextFutureMinimum` とし、既存の `FutureMinima.IsStandard` は
隣接 pair がすべてその局所条件を満たす compatibility view として扱う。

Adjacent-return の suffix geometry に必要なのはこちらの局所最小性であり、
Record--Ferrers の positive roof anchor とは別層の actual semantics である。
-/

namespace Collatz3
namespace OddOrbit
namespace FutureMinima

/--
次項が current より後の任意の軌道値以下、という標準隣接性。

どの witness を使って標準列を構成したかには依存せず、
後段の幾何が本当に必要とする性質だけを表す。
-/
def IsStandard
    {O : OddOrbit}
    (S : O.FutureMinima) : Prop :=
  ∀ j t : ℕ,
    S.index j < t →
      O.value (S.index (j + 1)) ≤ O.value t

/-- 標準列の次項は current より後の各位置の値以下。 -/
theorem next_value_le_of_standard
    {O : OddOrbit}
    {S : O.FutureMinima}
    (hStandard : S.IsStandard)
    {j t : ℕ}
    (hjt : S.index j < t) :
    O.value (S.index (j + 1)) ≤ O.value t :=
  hStandard j t hjt

/--
`IsStandard` は、各隣接 pair が局所正本 `NextFutureMinimum` であることと同値。
無限列に固有の追加情報はない。
-/
theorem isStandard_iff_nextFutureMinimum
    {O : OddOrbit}
    (S : O.FutureMinima) :
    S.IsStandard ↔
      ∀ j : ℕ,
        O.NextFutureMinimum (S.index j) (S.index (j + 1)) := by
  constructor
  · intro h j
    refine ⟨S.index_strict (Nat.lt_succ_self j), ?_⟩
    intro t hjt
    exact h j t hjt
  · intro h j t hjt
    exact (h j).2 t hjt

end FutureMinima
end OddOrbit
end Collatz3
