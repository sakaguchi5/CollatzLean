import CollatzLean.Collatz3.Semantics.Sufficiency
import CollatzLean.Collatz3.Semantics.ReachOne

/-!
# Collatz3: sufficient set から 1 到達への一般帰結

`OddSufficient S` は「任意の正の奇数が、`S` のある元と有限時間後に合流する」
ことだけを表す薄い語彙である。

重要なのは、`Merges x a` だけから直ちに `Reaches x 1` としていないことである。
まず odd-only Collatz では `1` から始まる有限 run の終点が常に `1` であることを
決定性から証明し、その後で「合流は 1 到達性を輸送する」ことを theorem として導く。

Monks 型の arithmetic progression の十分性はここでは仮定しない。
したがって以下は、将来どの sufficient set を使う場合にも再利用できる一般定理である。
-/

namespace Collatz3

namespace Runs

/-- `1` から始まる finite odd-only run の終点は必ず `1`。 -/
theorem end_eq_one_of_start_one
    {w : Word} {y : ℕ}
    (h : Runs w 1 y) :
    y = 1 := by
  induction w generalizing y with
  | nil =>
      cases h
      rfl
  | cons e w ih =>
      cases h with
      | @cons _ _ _ m _ hstep htail =>
          have hm : m = 1 :=
            (OddStep.deterministic hstep OddStep.one_self).2
          subst m
          exact ih htail

end Runs

namespace Reaches

/-- `1` から finite odd-only 到達できる値は `1` 自身だけ。 -/
theorem eq_one_of_one_reaches
    {y : ℕ}
    (h : Reaches 1 y) :
    y = 1 := by
  rcases h with ⟨w, hw⟩
  exact Runs.end_eq_one_of_start_one hw

end Reaches

namespace Merges

/--
`x` が `a` と合流し、`a` が `1` に到達するなら、`x` も `1` に到達する。

共通合流点を `z` とする。`a` からは `z` と `1` の両方へ到達するので、
前向き軌道の決定性により `z → 1` または `1 → z` のどちらかである。
前者ならそのまま連結でき、後者なら `1` の軌道は `1` だけなので `z = 1` となる。
-/
theorem reaches_one_of_right_reaches_one
    {x a : ℕ}
    (hMerge : Merges x a)
    (haOne : Reaches a 1) :
    Reaches x 1 := by
  rcases hMerge with ⟨z, hxz, haz⟩
  rcases Reaches.comparable_of_common_start haz haOne with hzOne | hOneZ
  · exact Reaches.trans hxz hzOne
  · have hz : z = 1 := Reaches.eq_one_of_one_reaches hOneZ
    subst z
    exact hxz

end Merges

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
  exact Merges.reaches_one_of_right_reaches_one hxa (hSOne a haS)

end OddSufficient
end Collatz3
