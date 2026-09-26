import CollatzLean.Collatz4.Dynamics.Accumulated
import CollatzLean.Collatz4.Dynamics.Reachability


/-!
# Collatz4.Dynamics.Merge

決定的な Collatz 軌道における「一度合流したら、その後は永久に一致する」を
一般定理として切り出す。

ここでは奇数圧縮軌道 `oddRun` と、累積 2 指数を保持する `accumulatedRun` の
両方について同じ構造を証明する。
-/

namespace Collatz4.Dynamics

/-- `accumulatedRun` の最後の 1 step を右側へ取り出す。 -/
theorem accumulatedRun_succ_last (k A : ℕ) :
    accumulatedRun (k + 1) A = accumulatedStep (accumulatedRun k A) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
      rw [accumulatedRun_succ]
      rw [ih]
      rw [accumulatedRun_succ]

/-- `oddRun` の最後の 1 step を右側へ取り出す一般補題。 -/
theorem oddRun_succ_last_general (k x : ℕ) :
    oddRun (k + 1) x = oddStep (oddRun k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [oddRun_succ]
      rw [ih]
      rw [oddRun_succ]

/-- 累積軌道を `a` 回と `b` 回に分割しても同じ。 -/
theorem accumulatedRun_add (a b A : ℕ) :
    accumulatedRun (a + b) A =
      accumulatedRun b (accumulatedRun a A) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      rw [hab, accumulatedRun_succ_last, ih]
      rw [← accumulatedRun_succ_last]

/-- 奇数圧縮軌道を `a` 回と `b` 回に分割しても同じ。 -/
theorem oddRun_add_general (a b x : ℕ) :
    oddRun (a + b) x = oddRun b (oddRun a x) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      rw [hab, oddRun_succ_last_general, ih]
      rw [← oddRun_succ_last_general]

/--
累積軌道が時刻 `a`,`b` で合流したなら、同じ追加 step 数だけ進めた後も一致する。
-/
theorem accumulatedRun_eq_of_merge
    {x y a b : ℕ}
    (hmerge : accumulatedRun a x = accumulatedRun b y)
    (k : ℕ) :
    accumulatedRun (a + k) x = accumulatedRun (b + k) y := by
  rw [accumulatedRun_add, accumulatedRun_add, hmerge]

/--
奇数圧縮軌道が時刻 `a`,`b` で合流したなら、その後の軌道は永久に一致する。
-/
theorem oddRun_eq_of_merge
    {x y a b : ℕ}
    (hmerge : oddRun a x = oddRun b y)
    (k : ℕ) :
    oddRun (a + k) x = oddRun (b + k) y := by
  rw [oddRun_add_general, oddRun_add_general, hmerge]

/-- 同じ時刻で合流した累積軌道は、以後すべての同時刻で一致する。 -/
theorem accumulatedRun_eq_of_same_time_merge
    {x y s : ℕ}
    (hmerge : accumulatedRun s x = accumulatedRun s y) :
    ∀ k : ℕ, accumulatedRun (s + k) x = accumulatedRun (s + k) y := by
  intro k
  exact accumulatedRun_eq_of_merge hmerge k

/-- 同じ時刻で合流した奇数圧縮軌道は、以後すべての同時刻で一致する。 -/
theorem oddRun_eq_of_same_time_merge
    {x y s : ℕ}
    (hmerge : oddRun s x = oddRun s y) :
    ∀ k : ℕ, oddRun (s + k) x = oddRun (s + k) y := by
  intro k
  exact oddRun_eq_of_merge hmerge k

end Collatz4.Dynamics
