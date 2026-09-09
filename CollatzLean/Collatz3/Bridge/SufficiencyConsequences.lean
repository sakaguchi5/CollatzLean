import CollatzLean.Collatz3.Semantics.Sufficiency
import CollatzLean.Collatz3.Semantics.ReachOneMerge

/-!
# Collatz3: sufficient set から 1 到達への一般帰結

`OddSufficient S` は「任意の正の奇数が、`S` のある元と有限時間後に合流する」
ことだけを表す薄い語彙である。

`1` からの run の一意性や、merge class 上の `ReachesOne` 不変性は
Semantics 層へ移した。この Bridge は sufficient set に固有の高位 corollary だけを持つ。

Monks 型の arithmetic progression の十分性はここでは仮定しない。
-/

namespace Collatz3
namespace OddSufficient

/--
`S` が odd-only sufficient で、`S` の全要素が `1` に到達するなら、
すべての正の奇数が `1` に到達する。

これは sufficient set を用いた全体帰着の一般形であり、
`S` が等差数列であることや 3 進条件を持つことは仮定していない。
-/
theorem all_positive_odds_reach_one
    {S : ℕ → Prop}
    (hS : OddSufficient S)
    (hSOne : ∀ a : ℕ, S a → Reaches a 1) :
    ∀ x : ℕ, 0 < x → Odd x → Reaches x 1 := by
  intro x hxPos hxOdd
  rcases hS x hxPos hxOdd with ⟨a, haS, hxa⟩
  have haOne : ReachesOne a := by
    change Reaches a 1
    exact hSOne a haS
  have hxOne : ReachesOne x :=
    (Merges.reachesOne_iff hxa).2 haOne
  change Reaches x 1 at hxOne
  exact hxOne

end OddSufficient
end Collatz3
