import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Multiplicity

/-!
# Collatz4.Dynamics.Odd

任意の自然数に適用できる奇数圧縮 Collatz 写像の最小定義。

この層は Collatz4 の研究対象を広げるためのものではない。
`101, 1011, 10111, ...` 族の証明中に得られた、一般の Collatz 軌道にも
適用できる定理を置くための道具箱である。
-/

namespace Collatz4.Dynamics

/-- `3n+1` から 2 の最大冪を除いた奇数圧縮写像。 -/
def oddStep (n : ℕ) : ℕ :=
  (3 * n + 1).divMaxPow 2

/-- `oddStep` を指定回数だけ反復する。 -/
def oddRun : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => oddRun k (oddStep x)

@[simp] theorem oddRun_zero (x : ℕ) : oddRun 0 x = x := rfl

@[simp] theorem oddRun_succ (k x : ℕ) :
    oddRun (k + 1) x = oddRun k (oddStep x) := rfl

end Collatz4.Dynamics
