import CollatzLean.Collatz4.Family.Basic

/-!
# Collatz4.Family.Branch

研究対象 `A_n = 3*2^n-1` の先頭で現れる標準形を定義する。

`branchPoint m r = 3^(r+1) * 2^(m-r) - 1`

は、これまで m-枝の固有 prefix と呼んでいた点を統一的に表す。
-/

namespace Collatz4.Family

/-- m 枝の r 番目の標準点。使用時には通常 `r < m` を仮定する。 -/
def branchPoint (m r : ℕ) : ℕ :=
  3 ^ (r + 1) * 2 ^ (m - r) - 1

@[simp] theorem branchPoint_zero (m : ℕ) :
    branchPoint m 0 = start m := by
  simp [branchPoint, start]

/-- `x` が m 枝の固有 prefix のどこかにある。 -/
def InBranchPrefix (m x : ℕ) : Prop :=
  ∃ r : ℕ, r < m ∧ x = branchPoint m r

end Collatz4.Family
