import CollatzLean.Collatz4.Family.Research

/-!
# Collatz4.Parametric.Reachability

`M` を変数にした Collatz4 内部の reachability を定義する。

この層は一般の Collatz 軌道全体へ研究対象を広げるものではなく、
`A_n = 3*2^n-1` 族の中で target branch `M` を変数にする一般化である。
-/

namespace Collatz4.Parametric

/-- 族の n 枝が M 枝の固有 prefix に到達する。 -/
def ReachesBranch (n M : ℕ) : Prop :=
  ∃ r : ℕ, r < M ∧
    Collatz4.Dynamics.Reaches
      (Collatz4.Family.start n)
      (Collatz4.Family.branchPoint M r)

/-- どれかの族の枝から M 枝へ到達できる。 -/
def BranchReachable (M : ℕ) : Prop :=
  ∃ n : ℕ, ReachesBranch n M

/-- 偶数添字の族の枝から M 枝へ到達できる。 -/
def EvenBranchReachable (M : ℕ) : Prop :=
  ∃ n : ℕ, n % 2 = 0 ∧ ReachesBranch n M

/-- `Q_N` から M 枝の固有 prefix に到達する。 -/
def QReachesBranch (N M : ℕ) : Prop :=
  ∃ r : ℕ, r < M ∧
    Collatz4.Dynamics.Reaches
      (Collatz4.Family.qStart N)
      (Collatz4.Family.branchPoint M r)

/-- 奇数 N の `Q_N` のどれかから M 枝へ到達できる。 -/
def OddQBranchReachable (M : ℕ) : Prop :=
  ∃ N : ℕ, N % 2 = 1 ∧ QReachesBranch N M

end Collatz4.Parametric
