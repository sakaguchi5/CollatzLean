import CollatzLean.Collatz3.Semantics.ReachOne

/-!
# Collatz3: 合流と `1` 到達性

`Merges` が保持するのは共通後続点の存在だけである。
odd-only dynamics の有限決定性により、`1` への有限到達性は merge class 上で不変になる。
-/

namespace Collatz3

namespace Runs

/-- `1` から始まる finite actual run の終点は `1`。Semantics 側の基本形。 -/
theorem end_eq_one_of_start_eq_one
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
            OddStep.end_eq_one_of_start_eq_one hstep
          subst m
          exact ih htail

end Runs

namespace Merges

/--
`x` と `y` が merge するなら、`x` の `1` 到達性は `y` へ輸送される。
-/
theorem reachesOne_of_left
    {x y : ℕ}
    (hMerge : Merges x y)
    (hxOne : ReachesOne x) :
    ReachesOne y := by
  rcases hMerge with ⟨z, hxz, hyz⟩
  change Reaches x 1 at hxOne
  rcases Reaches.comparable_of_common_start hxz hxOne with hzOne | hOneZ
  · change Reaches y 1
    exact Reaches.trans hyz hzOne
  · rcases hOneZ with ⟨w, hw⟩
    have hz : z = 1 := Runs.end_eq_one_of_start_eq_one hw
    subst z
    change Reaches y 1
    exact hyz

/-- `ReachesOne` は merge class 上で exact に不変。 -/
theorem reachesOne_iff
    {x y : ℕ}
    (hMerge : Merges x y) :
    ReachesOne x ↔ ReachesOne y := by
  constructor
  · intro hx
    exact Merges.reachesOne_of_left hMerge hx
  · intro hy
    exact Merges.reachesOne_of_left hMerge.symm hy

end Merges
end Collatz3
