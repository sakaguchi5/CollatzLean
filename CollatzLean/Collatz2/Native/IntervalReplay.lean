import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Core.Interval

/-!
# Collatz2 Native: interval replay

replay 用の新しい data package は導入しない。
lossless `Runs` を既存の `Interval` / `Interval.Split` で分解し、
各 nonempty body に既存 `ReplayCoordinate` が存在することだけを示す。
-/

namespace Collatz2
namespace Runs

/--
whole run を interval で分解すると、nonempty body は replay coordinate を持つ。
-/
theorem interval_replay
    {w : Word} {x z : ℕ}
    (h : Runs w x z)
    (I : Interval w)
    (hne : I.body ≠ []) :
    ∃ a b : ℕ,
      Runs I.left x a ∧
      Runs I.body a b ∧
      Runs I.right b z ∧
      Nonempty (Word.ReplayCoordinate I.body a b) := by
  obtain ⟨a, b, hleft, hbody, hright⟩ := h.split_interval I
  exact
    ⟨a, b, hleft, hbody, hright,
      ⟨Word.ReplayCoordinate.ofRuns hbody hne⟩⟩

/--
`Interval.Split` の中央二 body がともに nonempty なら、
両方の actual run と replay coordinate を同時に取り出せる。
-/
theorem split_replays
    {w : Word} {x z : ℕ}
    (h : Runs w x z)
    (S : Interval.Split w)
    (hfirst : S.first ≠ [])
    (hsecond : S.second ≠ []) :
    ∃ a b c : ℕ,
      Runs S.left x a ∧
      Runs S.first a b ∧
      Runs S.second b c ∧
      Runs S.right c z ∧
      Nonempty (Word.ReplayCoordinate S.first a b) ∧
      Nonempty (Word.ReplayCoordinate S.second b c) := by
  have hdecomp :
      Runs (S.left ++ S.first ++ S.second ++ S.right) x z := by
    rw [← S.decomp]
    exact h
  have h' :
      Runs (S.left ++ (S.first ++ (S.second ++ S.right))) x z := by
    simpa [List.append_assoc] using hdecomp
  obtain ⟨a, hleft, hrest₁⟩ := Runs.split_append h'
  obtain ⟨b, hfirstRun, hrest₂⟩ := Runs.split_append hrest₁
  obtain ⟨c, hsecondRun, hright⟩ := Runs.split_append hrest₂
  exact
    ⟨a, b, c, hleft, hfirstRun, hsecondRun, hright,
      ⟨Word.ReplayCoordinate.ofRuns hfirstRun hfirst⟩,
      ⟨Word.ReplayCoordinate.ofRuns hsecondRun hsecond⟩⟩

end Runs
end Collatz2
