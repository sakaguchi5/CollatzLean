import Mathlib.Data.List.Basic

/-!
# Collatz3: 有限指数語

odd-only Collatz の各奇数ステップで除く 2 の指数だけを保持する。

ここでは affine transfer、canonical residue、first passage などを導入しない。
-/

namespace Collatz3

/-- odd-only Collatz step の 2 除算指数を並べた有限語。 -/
abbrev Word := List ℕ

namespace Word

/-- すべての指数が正。 -/
def Valid (w : Word) : Prop :=
  ∀ e ∈ w, 0 < e

/-- 奇数ステップ数。 -/
def oddSteps (w : Word) : ℕ :=
  w.length

/-- 総 2 除算指数。 -/
def twoSteps (w : Word) : ℕ :=
  w.sum

/--
先頭 `k` odd steps までの累積 2 除算指数。

`k` が word の長さを超える場合は word 全体の `twoSteps` になる。
-/
def prefixTwoDepth (w : Word) (k : ℕ) : ℕ :=
  twoSteps (w.take k)

@[simp] theorem oddSteps_nil :
    oddSteps ([] : Word) = 0 := rfl

@[simp] theorem twoSteps_nil :
    twoSteps ([] : Word) = 0 := rfl

@[simp] theorem prefixTwoDepth_nil (k : ℕ) :
    prefixTwoDepth ([] : Word) k = 0 := by
  simp [prefixTwoDepth]

@[simp] theorem prefixTwoDepth_zero (w : Word) :
    prefixTwoDepth w 0 = 0 := by
  simp [prefixTwoDepth]

@[simp] theorem oddSteps_cons (e : ℕ) (w : Word) :
    oddSteps (e :: w) = oddSteps w + 1 := by
  simp [oddSteps]

@[simp] theorem twoSteps_cons (e : ℕ) (w : Word) :
    twoSteps (e :: w) = e + twoSteps w := by
  simp [twoSteps]

@[simp] theorem prefixTwoDepth_cons_succ
    (e : ℕ) (w : Word) (k : ℕ) :
    prefixTwoDepth (e :: w) (k + 1) =
      e + prefixTwoDepth w k := by
  simp [prefixTwoDepth, twoSteps]

@[simp] theorem oddSteps_append (u v : Word) :
    oddSteps (u ++ v) = oddSteps u + oddSteps v := by
  simp [oddSteps]

@[simp] theorem twoSteps_append (u v : Word) :
    twoSteps (u ++ v) = twoSteps u + twoSteps v := by
  simp [twoSteps]

/-- word 全長までの prefix 2-depth は `twoSteps` そのもの。 -/
@[simp] theorem prefixTwoDepth_oddSteps (w : Word) :
    prefixTwoDepth w (oddSteps w) = twoSteps w := by
  simp [prefixTwoDepth, oddSteps]

/-- valid 性は連結で保存される。 -/
theorem Valid.append {u v : Word}
    (hu : Valid u) (hv : Valid v) :
    Valid (u ++ v) := by
  intro e he
  rw [List.mem_append] at he
  exact he.elim (hu e) (hv e)

/-- valid 語の prefix は valid。 -/
theorem Valid.prefix {u v : Word}
    (h : Valid (u ++ v)) : Valid u := by
  intro e he
  exact h e (by simp [he])

/-- valid 語の suffix は valid。 -/
theorem Valid.suffix {u v : Word}
    (h : Valid (u ++ v)) : Valid v := by
  intro e he
  exact h e (by simp [he])

end Word

end Collatz3
