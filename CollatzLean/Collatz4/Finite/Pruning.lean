import CollatzLean.Collatz4.Finite.Forward

/-!
# Collatz4.Finite.Pruning

前向き探索の枝刈り条件を m 固有定数から分離する。

実際の数値 threshold は特殊化側の `LiveTarget` / `CheckpointSpec` に入れる。
-/

namespace Collatz4.Finite

/-- 共通終端時刻と目標2指数。 -/
structure LiveTarget where
  targetTime : ℕ
  targetTwoExponent : ℕ
  deriving Repr

/--
時刻 s の状態が目標へ届くための基本必要条件。
`u=1` を除き、残り各段で最低1だけ2指数が増えるという使い方を想定する。
-/
def liveNecessary (spec : LiveTarget) (s : ℕ) (x : ForwardState) : Prop :=
  x.u ≠ 1 ∧ x.t + (spec.targetTime - s) ≤ spec.targetTwoExponent

/-- checkpoint で使う三分岐の数値パラメータ。 -/
structure CheckpointSpec where
  upperCut : ℕ
  lowerCut : ℕ
  modulus : ℕ
  residue : ℕ
  deriving Repr

/--
checkpoint の安全側を表す一般三分岐。
数値の妥当性そのものは各特殊化側で certificate として証明する。
-/
def checkpointSafe (spec : CheckpointSpec) (x : ForwardState) : Prop :=
  x.u = 1 ∨
  spec.upperCut ≤ x.t ∨
  (x.t ≤ spec.lowerCut ∧ x.u % spec.modulus ≠ spec.residue)

end Collatz4.Finite
