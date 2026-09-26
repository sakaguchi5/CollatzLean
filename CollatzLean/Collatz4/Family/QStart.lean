import CollatzLean.Collatz4.Family.Branch

/-!
# Collatz4.Family.QStart

偶数添字枝を初期の決定的 prefix から切り離した後に現れる
三進 repunit 型の状態 `Q_N = (3^N - 1)/2` を定義する。
-/

namespace Collatz4.Family

/-- 三進数で `111...111` (N桁) に対応する値。 -/
def qStart (N : ℕ) : ℕ :=
  (3 ^ N - 1) / 2

@[simp] theorem qStart_one : qStart 1 = 1 := by
  decide

end Collatz4.Family
