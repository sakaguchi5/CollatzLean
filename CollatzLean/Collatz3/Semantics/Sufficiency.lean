import CollatzLean.Collatz3.Semantics.Reachability

/-!
# Collatz3: odd-only sufficient set の薄い語彙

ここでの `OddSufficient` は、現在の Collatz3 が採用している accelerated odd-only
semantics に限定した語彙である。

Monks の原定理で使われる full Collatz map 上の `sufficient` を、この定義と同一視しない。
full map と odd-only map の merge 関係を接続する bridge を後段で証明した後に、
Monks 型の arithmetic progression sufficiency を輸送する。
-/

namespace Collatz3

/--
正の奇数 `x` ごとに、述語 `S` を満たし `x` と合流する入口が存在する。
`S` 自身に算術的・canonical な条件は埋め込まない。
-/
def OddSufficient (S : ℕ → Prop) : Prop :=
  ∀ x : ℕ,
    0 < x →
    Odd x →
    ∃ a : ℕ, S a ∧ Merges x a

namespace OddSufficient

/-- sufficient 性から、指定した正の奇数に対する合流入口を取り出す。 -/
theorem entry
    {S : ℕ → Prop}
    (hS : OddSufficient S)
    {x : ℕ}
    (hxPos : 0 < x)
    (hxOdd : Odd x) :
    ∃ a : ℕ, S a ∧ Merges x a :=
  hS x hxPos hxOdd

/-- sufficient 集合を大きくしても sufficient 性は保存される。 -/
theorem mono
    {S T : ℕ → Prop}
    (hS : OddSufficient S)
    (hST : ∀ n : ℕ, S n → T n) :
    OddSufficient T := by
  intro x hxPos hxOdd
  rcases hS x hxPos hxOdd with ⟨a, haS, hxa⟩
  exact ⟨a, hST a haS, hxa⟩

/-- すべての正の奇数を含む述語は odd-only sufficient。 -/
theorem of_contains_all_positive_odds
    {S : ℕ → Prop}
    (hS : ∀ x : ℕ, 0 < x → Odd x → S x) :
    OddSufficient S := by
  intro x hxPos hxOdd
  exact ⟨x, hS x hxPos hxOdd, Merges.refl x⟩

end OddSufficient
end Collatz3
