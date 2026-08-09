import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 有限指数語の代数核

odd-only Collatz写像の有限指数語と、そのアフィン量を定義する。
無限軌道・canonical選択・future minimumには依存しない。
-/

namespace Collatz

/-- odd-only Collatz写像で使う2除算指数の有限語。 -/
abbrev Word := List ℕ

namespace Word

/-- すべての指数が正。 -/
def Valid (w : Collatz.Word) : Prop := ∀ e ∈ w, 0 < e

/-- 奇数操作数。 -/
def oddSteps (w : Collatz.Word) : ℕ := w.length

/-- 総2除算数。 -/
def twoSteps (w : Collatz.Word) : ℕ := w.sum

/-- `2^H y = 3^p x + B` のアフィン定数。 -/
def affineConst : Collatz.Word → ℕ
  | [] => 0
  | e :: w => 3 ^ w.length + 2 ^ e * affineConst w

/-- アフィン定数の整数版。 -/
def affineConstInt (w : Collatz.Word) : ℤ := affineConst w

/-- `3^p - 2^H`。 -/
def determinant (w : Collatz.Word) : ℤ :=
  (3 : ℤ) ^ w.oddSteps - (2 : ℤ) ^ w.twoSteps

/-- 有限語の自然数上のアフィン実現式。 -/
def Realizes (w : Collatz.Word) (x y : ℕ) : Prop :=
  2 ^ w.twoSteps * y = 3 ^ w.oddSteps * x + w.affineConst

/-- 有限語の整数上のアフィン実現式。 -/
def RealizesInt (w : Collatz.Word) (x y : ℤ) : Prop :=
  (2 : ℤ) ^ w.twoSteps * y =
    (3 : ℤ) ^ w.oddSteps * x + w.affineConstInt

/-- `Y = X + 2^λ u` かつ `u` が奇数。 -/
def IsReturn (X Y lambda u : ℕ) : Prop :=
  Y = X + 2 ^ lambda * u ∧ Odd u

/-- 純乗法係数が膨張側。 -/
def Expanding (w : Collatz.Word) : Prop :=
  2 ^ w.twoSteps < 3 ^ w.oddSteps

/-- 純乗法係数が収縮側。 -/
def Contracting (w : Collatz.Word) : Prop :=
  3 ^ w.oddSteps < 2 ^ w.twoSteps

@[simp] theorem oddSteps_nil : oddSteps ([] : Collatz.Word) = 0 := rfl
@[simp] theorem twoSteps_nil : twoSteps ([] : Collatz.Word) = 0 := rfl
@[simp] theorem affineConst_nil : affineConst ([] : Collatz.Word) = 0 := rfl

@[simp] theorem oddSteps_cons (e : ℕ) (w : Collatz.Word) :
    oddSteps (e :: w) = oddSteps w + 1 := by
  rfl
@[simp] theorem twoSteps_cons (e : ℕ) (w : Collatz.Word) :
    twoSteps (e :: w) = e + w.twoSteps := by simp [twoSteps]

@[simp] theorem affineConst_cons (e : ℕ) (w : Collatz.Word) :
    affineConst (e :: w)= 3 ^ w.oddSteps + 2 ^ e * w.affineConst := rfl

@[simp] theorem oddSteps_append (u v : Collatz.Word) :
    (u ++ v).oddSteps = u.oddSteps + v.oddSteps := by simp [oddSteps]

@[simp] theorem twoSteps_append (u v : Collatz.Word) :
    (u ++ v).twoSteps = u.twoSteps + v.twoSteps := by simp [twoSteps]

/-- アフィン定数の連結公式。 -/
theorem affineConst_append (u v : Collatz.Word) :
    (u ++ v).affineConst =
      3 ^ v.oddSteps * u.affineConst +
      2 ^ u.twoSteps * v.affineConst := by
  induction u with
  | nil => simp [affineConst]
  | cons e u ih =>
      simp only [List.cons_append, affineConst_cons, oddSteps_append,
        twoSteps_cons, ih]
      rw [pow_add, pow_add]
      ring

/-- determinantの連結公式。 -/
theorem determinant_append (u v : Collatz.Word) :
    (u ++ v).determinant =
      (3 : ℤ) ^ v.oddSteps * u.determinant +
      (2 : ℤ) ^ u.twoSteps * v.determinant := by
  simp only [determinant, oddSteps_append, twoSteps_append]
  rw [pow_add, pow_add]
  ring

/-- valid性は連結で保存。 -/
theorem Valid.append {u v : Collatz.Word} (hu : u.Valid) (hv : v.Valid) :
    (u ++ v).Valid := by
  intro e he
  rw [List.mem_append] at he
  exact he.elim (hu e) (hv e)

/-- validな語のprefixもvalid。 -/
theorem Valid.prefix {u v : Collatz.Word} (h : (u ++ v).Valid) : u.Valid := by
  intro e he
  exact h e (by simp [he])

/-- valid語では奇数操作数以下の2除算を必ず消費する。 -/
theorem oddSteps_le_twoSteps {w : Collatz.Word} (hw : w.Valid) :
    w.oddSteps ≤ w.twoSteps := by
  induction w with
  | nil => simp [oddSteps, twoSteps]
  | cons e w ih =>
      have he : 0 < e := hw e (by simp)
      have htail : Valid w := by
        intro a ha
        exact hw a (by simp [ha])
      have hi := ih htail
      simp only [oddSteps_cons, twoSteps_cons]
      omega

/-- validな非空語の総2除算数は正。 -/
theorem twoSteps_pos_of_valid_nonempty {w : Collatz.Word}
    (hw : w.Valid) (hne : w ≠ []) : 0 < w.twoSteps := by
  cases w with
  | nil => contradiction
  | cons e w =>
      have he : 0 < e := hw e (by simp)
      simp only [twoSteps_cons]
      omega

end Word
end Collatz
