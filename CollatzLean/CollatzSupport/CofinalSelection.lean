import Mathlib.Data.Nat.Factorization.Defs

/-!
# 自然数添字族のcofinal選択

Collatz固有ではない無限部分列選択を集約する。
-/

namespace CollatzSupport

/-- 命題が任意に遠い自然数添字で成立すること。 -/
def Cofinally (P : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n

namespace Cofinally

/-- cofinalな命題を満たす添字を狭義単調に選ぶ。 -/
noncomputable def select
    (P : ℕ → Prop)
    (h : Cofinally P) : ℕ → ℕ
  | 0 => Classical.choose (h 0)
  | n + 1 => Classical.choose (h (select P h n + 1))

/-- 選択添字は自身以上。 -/
theorem select_ge
    (P : ℕ → Prop)
    (h : Cofinally P) :
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
theorem select_strict
    (P : ℕ → Prop)
    (h : Cofinally P) :
    StrictMono (select P h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := Classical.choose_spec (h (select P h n + 1))
  simpa [select] using hs.1

/-- 選択された各添字では命題が成立する。 -/
theorem select_spec
    (P : ℕ → Prop)
    (h : Cofinally P)
    (n : ℕ) :
    P (select P h n) := by
  cases n with
  | zero => simpa [select] using (Classical.choose_spec (h 0)).2
  | succ n =>
      simpa [select] using
        (Classical.choose_spec (h (select P h n + 1))).2

/-- cofinalでなければ、十分後には命題が成立しない。 -/
theorem eventually_not_of_not
    (P : ℕ → Prop)
    (h : ¬ Cofinally P) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ P n := by
  unfold Cofinally at h
  push Not at h
  exact h

end Cofinally
end CollatzSupport
