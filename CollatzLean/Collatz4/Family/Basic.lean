import CollatzLean.Collatz4.Dynamics.Reachability

/-!
# Collatz4.Family.Basic

Collatz4 の研究対象そのものを定義する。

`A n = 3 * 2^n - 1` (`n >= 1`) は二進数で

`101, 1011, 10111, 101111, ...`

となる族である。Collatz4 はこの族から始まる Collatz 軌道を研究する。
一般の Collatz 予想そのものを研究対象にはしない。
-/

namespace Collatz4.Family

/-- 二進数 `10` の後ろに `n` 個の `1` が続く研究対象。 -/
def start (n : ℕ) : ℕ :=
  3 * 2 ^ n - 1

@[simp] theorem start_one : start 1 = 5 := by
  decide

@[simp] theorem start_two : start 2 = 11 := by
  decide

@[simp] theorem start_three : start 3 = 23 := by
  decide

/-- 添字を1増やすことは、二進表記の末尾へ `1` を1個追加することに対応する。 -/
theorem start_succ (n : ℕ) :
    start (n + 1) = 2 * start n + 1 := by
  simp only [start, pow_succ, Nat.pred_eq_succ_iff]
  have h : 0 < 3 * 2 ^ n := by positivity
  omega

end Collatz4.Family
