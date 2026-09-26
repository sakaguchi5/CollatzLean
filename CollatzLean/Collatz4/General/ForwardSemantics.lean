import CollatzLean.Collatz4.Core.Forward

/-!
# Collatz4.General.ForwardSemantics

前向き `step` の意味論を、有限計算 `run` から独立に記述する一般層。

`ResidualRecurrence k x z` は、状態 `x` から `step` を正確に `k` 回つないで
状態 `z` に到達することを表す。各 m の数論的 witness は、具体的な残余語から
この recurrence を供給すればよい。
-/

namespace Collatz4.General

/--
`step` をちょうど指定回数だけつないだ意味論的 recurrence。

`run` の実装そのものを仮定にせず、1段ずつの遷移だけで定義する。
-/
inductive ResidualRecurrence : ℕ → ForwardState → ForwardState → Prop
  | zero (x : ForwardState) : ResidualRecurrence 0 x x
  | succ {k : ℕ} {x z : ForwardState} :
      ResidualRecurrence k (Collatz4.step x) z →
      ResidualRecurrence (k + 1) x z

/--
意味論的 recurrence と計算関数 `run` は一致する。

この定理により、数論側は1段ごとの recurrence だけを証明すればよく、
有限 certificate 側の `run` 実装へ直接依存しない。
-/
theorem run_eq_of_residual_recurrence
    {k : ℕ} {initial target : ForwardState}
    (h : ResidualRecurrence k initial target) :
    Collatz4.run k initial = target := by
  induction h with
  | zero x => rfl
  | succ h ih =>
      rw [Collatz4.run_succ]
      exact ih

end Collatz4.General
