import CollatzLean.Collatz3.Semantics.FutureMinimum

/-!
# Collatz3: standard future-minimum property

単なる future-minimum 部分列と、各 current の直後の tail 全体から最小値を選ぶ
**標準列**を分離する。

stable core では「どの標準列を classical に選ぶか」を定義しない。
後段の定理が本当に使う `IsStandard` という性質だけを公開し、
標準列そのものは証明付き入力として受け取る。

無限 tail の最小値を `Nat.find` / `Classical.choose` で一つ選ぶ従来の canonical constructor は
`StandardFutureMinimumChoice.lean` に隔離する。この choice ファイルは stable root から import しない。

Adjacent-return の suffix geometry に必要なのはこちらの `IsStandard` であり、
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

end FutureMinima
end OddOrbit
end Collatz3
