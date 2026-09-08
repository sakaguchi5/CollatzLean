import CollatzLean.Collatz3.Semantics.Reachability

/-!
# Collatz3: odd-only 逆向き前駆点

逆コラッツのために新しい step 方程式は導入しない。
前向きの正本 `OddStep e x y` を、終点 `y` から始点 `x` を読む view として再利用する。

このファイルでは、RecordFerrers や fixed-fiber excess を仮定しない。
逆向き意味論として必要な最小語彙と、そこから直ちに従う枝生成則だけを置く。
-/

namespace Collatz3

/--
`y` から逆向きに指数 `e` を選んで `x` へ移ることを表す view。
数学的内容の正本は前向きの `OddStep e x y` である。
-/
abbrev BackwardStep (e y x : ℕ) : Prop :=
  OddStep e x y

namespace BackwardStep

/-- 逆向きに読んでも指数は正。 -/
theorem exponent_pos
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    0 < e :=
  OddStep.exponent_pos h

/-- 逆向き 1 step の exact equation は `2^e * y = 3*x + 1`。 -/
theorem equation
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    2 ^ e * y = 3 * x + 1 :=
  OddStep.equation h

/-- 逆向き前駆点 `x` は奇数。 -/
theorem predecessor_odd
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    Odd x :=
  OddStep.start_odd h

/-- 逆向き step の根側 `y` は奇数。 -/
theorem target_odd
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    Odd y :=
  OddStep.end_odd h

/--
終点 `y` と指数 `e` を固定すると、odd-only 前駆点は高々一つ。
逆向きでは指数そのものは複数候補を持ちうるが、指数を固定した枝は一意である。
-/
theorem predecessor_unique
    {e y x z : ℕ}
    (hx : BackwardStep e y x)
    (hz : BackwardStep e y z) :
    x = z := by
  have hEq : 3 * x + 1 = 3 * z + 1 := by
    calc
      3 * x + 1 = 2 ^ e * y := (BackwardStep.equation hx).symm
      _ = 3 * z + 1 := BackwardStep.equation hz
  omega

/--
同じ終点 `y` へ入る枝で指数を `e` から `e+2` に増やすと、
前駆点は `x` から `4*x+1` へ移る。

これは逆コラッツ木の同一分岐族が `x ↦ 4*x+1` で並ぶことの基本形である。
-/
theorem add_two
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    BackwardStep (e + 2) y (4 * x + 1) := by
  refine ⟨by omega, ?_, BackwardStep.target_odd h⟩
  calc
    2 ^ (e + 2) * y = (2 ^ e * y) * 4 := by
      rw [pow_add]
      norm_num
      ring
    _ = (3 * x + 1) * 4 := by rw [BackwardStep.equation h]
    _ = 3 * (4 * x + 1) + 1 := by ring

end BackwardStep

/--
`x` が `y` の odd-only 前駆点であること。
指数を忘れ、ある正指数の exact `BackwardStep` が存在することだけを保持する。
-/
def IsPredecessor (x y : ℕ) : Prop :=
  ∃ e : ℕ, BackwardStep e y x

namespace IsPredecessor

/-- exact な逆向き 1 step は前駆点関係を与える。 -/
theorem of_backwardStep
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    IsPredecessor x y :=
  ⟨e, h⟩

/-- 前駆点は奇数。 -/
theorem predecessor_odd
    {x y : ℕ}
    (h : IsPredecessor x y) :
    Odd x := by
  rcases h with ⟨e, he⟩
  exact BackwardStep.predecessor_odd he

/-- 前駆点を持つ根側の値も奇数。 -/
theorem target_odd
    {x y : ℕ}
    (h : IsPredecessor x y) :
    Odd y := by
  rcases h with ⟨e, he⟩
  exact BackwardStep.target_odd he

/--
`3 ∣ y` なら `y` には odd-only 前駆点が存在しない。
`2^e*y` は 3 の倍数になる一方、exact equation の右辺 `3*x+1` は 3 の倍数ではない。
-/
theorem false_of_three_dvd_target
    {x y : ℕ}
    (h : IsPredecessor x y)
    (hy : 3 ∣ y) :
    False := by
  rcases h with ⟨e, he⟩
  rcases hy with ⟨k, rfl⟩
  have hEq : 3 * (2 ^ e * k) = 3 * x + 1 := by
    calc
      3 * (2 ^ e * k) = 2 ^ e * (3 * k) := by ring
      _ = 3 * x + 1 := BackwardStep.equation he
  omega

/-- `3 ∣ y` なら `y` の odd-only 前駆点は存在しない。 -/
theorem not_of_three_dvd_target
    {x y : ℕ}
    (hy : 3 ∣ y) :
    ¬ IsPredecessor x y := by
  intro h
  exact IsPredecessor.false_of_three_dvd_target h hy

/--
一つ前駆点 `x` が存在すれば、同じ `y` に入る次の枝 `4*x+1` も存在する。
これは指数を 2 増やす `BackwardStep.add_two` から導く。
-/
theorem four_mul_add_one
    {x y : ℕ}
    (h : IsPredecessor x y) :
    IsPredecessor (4 * x + 1) y := by
  rcases h with ⟨e, he⟩
  exact ⟨e + 2, BackwardStep.add_two he⟩

end IsPredecessor

/--
`y` から逆向きに有限個の odd-only step をたどって `x` に到達すること。
新しい run を定義せず、既存の前向き `Reaches x y` を逆向きに読む。
-/
abbrev BackwardReaches (y x : ℕ) : Prop :=
  Reaches x y

namespace BackwardReaches

/-- 任意の値は空 run を逆向きに読んでも自分自身へ到達する。 -/
@[refl]
theorem refl (x : ℕ) : BackwardReaches x x :=
  Reaches.refl x

/-- exact な逆向き 1 step は有限逆向き到達を与える。 -/
theorem of_backwardStep
    {e y x : ℕ}
    (h : BackwardStep e y x) :
    BackwardReaches y x :=
  Reaches.of_oddStep h

/--
逆向き有限到達は連結できる。
`z` から `y` へ、さらに `y` から `x` へ逆向きにたどれるなら、`z` から `x` へたどれる。
-/
theorem trans
    {x y z : ℕ}
    (hyx : BackwardReaches y x)
    (hzy : BackwardReaches z y) :
    BackwardReaches z x :=
  Reaches.trans hyx hzy

end BackwardReaches
end Collatz3
