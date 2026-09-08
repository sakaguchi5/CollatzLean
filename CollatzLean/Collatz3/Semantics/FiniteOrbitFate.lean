import CollatzLean.Collatz3.Semantics.OrbitFate

/-!
# Collatz3: 有限深度での構成的な軌道分類

無限軌道全体について「いつか起きる」事象を判定する前に、深さ `N` までの有限列だけを調べる。
ここでは有限型 `Fin (N + 1)` 上の等値判定だけを使うため、三分法は構成的に実行できる。

深さ `N` までには次のどれかが起きる。

1. `1` をすでに通った。
2. `1` 以外の同じ値をすでに二度通った。
3. まだ `1` に到達せず、値の重複もない。

無限軌道の完全三分法とは分離し、この有限三分法には classical choice を使わない。
-/

namespace Collatz3
namespace OddOrbit

/-- 時刻 `0,...,N` のどこかで `1` に到達している。 -/
def HitsOneThrough (O : OddOrbit) (N : ℕ) : Prop :=
  ∃ n : Fin (N + 1), O.value n = 1

/-- 時刻 `0,...,N` の範囲で `1` 以外の同じ値を二度通っている。 -/
def HasNontrivialRepeatThrough (O : OddOrbit) (N : ℕ) : Prop :=
  ∃ i j : Fin (N + 1),
    i < j ∧
    O.value i = O.value j ∧
    O.value i ≠ 1

/--
時刻 `0,...,N` ではまだ `1` に到達せず、値の重複もない。
有限探索がまだ閉じていない第3状態を表す。
-/
def OpenThrough (O : OddOrbit) (N : ℕ) : Prop :=
  (∀ n : Fin (N + 1), O.value n ≠ 1) ∧
    ∀ i j : Fin (N + 1), i < j → O.value i ≠ O.value j

instance hitsOneThroughDecidable
    (O : OddOrbit) (N : ℕ) :
    Decidable (O.HitsOneThrough N) := by
  unfold HitsOneThrough
  infer_instance

instance hasNontrivialRepeatThroughDecidable
    (O : OddOrbit) (N : ℕ) :
    Decidable (O.HasNontrivialRepeatThrough N) := by
  unfold HasNontrivialRepeatThrough
  infer_instance

/-- 有限深度の三分法。有限型上の判定だけなので classical choice は不要。 -/
theorem finiteFate_trichotomy
    (O : OddOrbit)
    (N : ℕ) :
    O.HitsOneThrough N ∨
      O.HasNontrivialRepeatThrough N ∨
      O.OpenThrough N := by
  by_cases hHit : O.HitsOneThrough N
  · exact Or.inl hHit
  · by_cases hRepeat : O.HasNontrivialRepeatThrough N
    · exact Or.inr (Or.inl hRepeat)
    · refine Or.inr (Or.inr ?_)
      constructor
      · intro n hnOne
        exact hHit ⟨n, hnOne⟩
      · intro i j hij heq
        have hiOne : O.value i ≠ 1 := by
          intro hi
          exact hHit ⟨i, hi⟩
        exact hRepeat ⟨i, j, hij, heq, hiOne⟩

/-- 有限深度ですでに `1` を通っていれば、無限軌道としても `HitsOne`。 -/
theorem hitsOne_of_hitsOneThrough
    (O : OddOrbit)
    {N : ℕ}
    (h : O.HitsOneThrough N) :
    O.HitsOne := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- 有限深度ですでに非自明な再訪があれば、無限軌道としても同じ再訪を持つ。 -/
theorem hasNontrivialRepeat_of_hasNontrivialRepeatThrough
    (O : OddOrbit)
    {N : ℕ}
    (h : O.HasNontrivialRepeatThrough N) :
    O.HasNontrivialRepeat := by
  rcases h with ⟨i, j, hij, heq, hiOne⟩
  exact ⟨i, j, hij, heq, hiOne⟩

end OddOrbit
end Collatz3
