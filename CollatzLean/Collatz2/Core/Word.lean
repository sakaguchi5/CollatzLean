import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# Collatz2: finite exponent words

`Collatz2` は旧 `Collatz` 名前空間に依存しない独立体系として構築する。
このファイルでは有限指数語と、その最小限の算術データだけを定義する。

`Expanding` / `Contracting` / canonical / replay などの射影概念はまだ導入しない。
-/

namespace Collatz2

/-- odd-only Collatz step の2除算指数を並べた有限語。 -/
abbrev Word := List ℕ

namespace Word

/-- 全指数が正である。 -/
def Valid (w : Word) : Prop :=
  ∀ e ∈ w, 0 < e

/-- odd step 数。 -/
def oddSteps (w : Word) : ℕ :=
  w.length

/-- 総2除算指数。 -/
def twoSteps (w : Word) : ℕ :=
  w.sum

/--
有限語に付随する affine translation。
後で `2^H * y = 3^p * x + affineConst` の形で使う。
-/
def affineConst : Word → ℕ
  | [] => 0
  | e :: w => 3 ^ w.length + 2 ^ e * affineConst w

@[simp] theorem oddSteps_nil : oddSteps ([] : Word) = 0 := rfl
@[simp] theorem twoSteps_nil : twoSteps ([] : Word) = 0 := rfl
@[simp] theorem affineConst_nil : affineConst ([] : Word) = 0 := rfl

@[simp] theorem oddSteps_cons (e : ℕ) (w : Word) :
    oddSteps (e :: w) = oddSteps w + 1 := by
  rfl

@[simp] theorem twoSteps_cons (e : ℕ) (w : Word) :
    twoSteps (e :: w) = e + twoSteps w := by
  simp [twoSteps]

@[simp] theorem affineConst_cons (e : ℕ) (w : Word) :
    affineConst (e :: w) =
      3 ^ oddSteps w + 2 ^ e * affineConst w := by
  rfl

@[simp] theorem oddSteps_append (u v : Word) :
    oddSteps (u ++ v) = oddSteps u + oddSteps v := by
  simp [oddSteps]

@[simp] theorem twoSteps_append (u v : Word) :
    twoSteps (u ++ v) = twoSteps u + twoSteps v := by
  simp [twoSteps]

/-- affine translation の連結公式。 -/
theorem affineConst_append (u v : Word) :
    affineConst (u ++ v) =
      3 ^ oddSteps v * affineConst u +
        2 ^ twoSteps u * affineConst v := by
  induction u with
  | nil =>
      simp [affineConst]
  | cons e u ih =>
      simp only [List.cons_append, affineConst_cons, oddSteps_append,
        twoSteps_cons, ih]
      rw [pow_add, pow_add]
      ring

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

/-- valid 非空語では総2除算指数が正。 -/
theorem twoSteps_pos_of_valid_nonempty
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    0 < twoSteps w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      have he : 0 < e := hvalid e (by simp)
      simp only [twoSteps_cons]
      omega

end Word
end Collatz2
