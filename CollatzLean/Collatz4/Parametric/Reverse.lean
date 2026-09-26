import CollatzLean.Collatz4.Parametric.Reachability

/-!
# Collatz4.Parametric.Reverse

M を変数にした逆向き reachability を記述するための最小語彙。

`inverseStep k y = (2^k*y-1)/3` は、整数条件を満たすとき奇数圧縮 Collatz の逆枝になる。
ここでは探索戦略を固定せず、今後 M=3,5,7,9,... の比較に使える定義だけを置く。
-/

namespace Collatz4.Parametric

/-- 2指数 k を指定した形式的な逆枝。 -/
def inverseStep (k y : ℕ) : ℕ :=
  (2 ^ k * y - 1) / 3

/-- `x+1` が 2 と 3 の冪だけから成る標準 branch point であること。 -/
def IsStandardBranchPoint (x : ℕ) : Prop :=
  ∃ M r : ℕ, r < M ∧ x = Collatz4.Family.branchPoint M r

end Collatz4.Parametric
