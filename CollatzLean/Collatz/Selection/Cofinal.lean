import Mathlib.Order.Monotone.Basic

/-!
# 無限添字選択

`noncomputable`な無限選択をこのファイルへ隔離する。
-/

namespace Collatz
namespace Selection

/-- 命題が任意に遠い自然数添字で成立する。 -/
def Cofinal (P : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n

namespace Cofinal

/-- cofinalな命題を満たす狭義単調列を選ぶ。 -/
noncomputable def select
    (P : ℕ → Prop) (h : Cofinal P) : ℕ → ℕ
  | 0 => Classical.choose (h 0)
  | n + 1 => Classical.choose (h (select P h n + 1))

/-- 選択添字は自身以上。 -/
theorem select_ge (P : ℕ → Prop) (h : Cofinal P) :
    ∀ n : ℕ, n ≤ select P h n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hs := Classical.choose_spec (h (select P h n + 1))
      have hstep : select P h n + 1 ≤ select P h (n + 1) := by
        simpa [select] using hs.1
      omega

/-- 選択列は狭義単調。 -/
theorem select_strict (P : ℕ → Prop) (h : Cofinal P) :
    StrictMono (select P h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := Classical.choose_spec (h (select P h n + 1))
  have hle :
      select P h n + 1 ≤ select P h (n + 1) := by
    simpa [select] using hs.1
  omega

/-- 選択された各添字では命題が成立。 -/
theorem select_spec (P : ℕ → Prop) (h : Cofinal P) (n : ℕ) :
    P (select P h n) := by
  cases n with
  | zero => simpa [select] using (Classical.choose_spec (h 0)).2
  | succ n => simpa [select] using
      (Classical.choose_spec (h (select P h n + 1))).2

/-- cofinalでなければ十分後には成立しない。 -/
theorem eventually_not_of_not
    (P : ℕ → Prop) (h : ¬ Cofinal P) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ P n := by
  unfold Cofinal at h
  push Not at h
  exact h

end Cofinal
end Selection
end Collatz
