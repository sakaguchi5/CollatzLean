import CollatzLean.Collatz4.Dynamics.Odd

/-!
# Collatz4.Dynamics.Reachability

一般の奇数圧縮 Collatz 軌道に対する reachability / merge の語彙。

ここには `101...` 族固有の定数や命題を置かない。
-/

namespace Collatz4.Dynamics

/-- `x` から有限回の奇数圧縮遷移で `y` に到達する。 -/
def Reaches (x y : ℕ) : Prop :=
  ∃ k : ℕ, oddRun k x = y

/-- 二つの軌道がどこかで合流する。 -/
def Merges (x y : ℕ) : Prop :=
  ∃ z : ℕ, Reaches x z ∧ Reaches y z

/-- 任意の点は0回で自分自身へ到達する。 -/
theorem reaches_refl (x : ℕ) : Reaches x x := by
  exact ⟨0, rfl⟩

/-- 1回の奇数圧縮遷移は reachability を与える。 -/
theorem reaches_step (x : ℕ) : Reaches x (oddStep x) := by
  exact ⟨1, rfl⟩

end Collatz4.Dynamics
