import CollatzLean.Collatz4.M7.ForwardReduction

/-!
# Collatz4.M7.LivePruning

有限 DAG を高速化するときに使う安全な枝刈り条件。
主定理は完全反復 certificate でも証明できるため、ここは一般補助層として独立させる。
-/

namespace Collatz4.M7

/--
時刻 `s` の状態がまだ目標に届く可能性を持つための必要条件。

* `u=1` は以後ずっと2のべきなので目標奇数部分へ戻れない。
* 残り各段で2指数は少なくとも1増えるので、最低増分だけで 10996 を
  超える状態は既に失敗している。
-/
def liveNecessary (s : ℕ) (x : ForwardState) : Prop :=
  x.u ≠ 1 ∧ x.t + (targetTime - s) ≤ targetTwoExponent

/-- 最後の1段前で使う安全述語。 -/
def checkpointSafe (x : ForwardState) : Prop :=
  x.u = 1 ∨
  11057 ≤ x.t ∨
  (x.t ≤ 10671 ∧ x.u % 64 ≠ 21)

end Collatz4.M7
