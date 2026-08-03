--import Mathlib
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# コラッツ奇数写像の有限語による代数核

このファイルでは、奇数のみを追跡するコラッツ写像

`x ↦ (3x+1)/2^e`

の指数列を有限語として表し、後続ファイルで共有する基本量を定義する。
解析的議論や無限軌道の仮定は一切入れない。
-/

namespace CollatzFirstLayer

/-- 奇数写像で使用する2除算指数の有限語。 -/
abbrev ExpWord := List ℕ

namespace ExpWord

/-- すべての指数が正であること。 -/
def Valid (w : ExpWord) : Prop := ∀ e ∈ w, 0 < e

/-- 語に含まれる奇数操作の回数。 -/
def oddSteps (w : ExpWord) : ℕ := w.length

/-- 語全体で消費する2除算回数。 -/
def twoSteps (w : ExpWord) : ℕ := w.sum

/--
語 `w` のアフィン定数 `B_w`。

`w = [e₁, …, eₚ]` を順に実行したとき、
`2^H y = 3^p x + B_w` となるように向きを固定している。
-/
def affineConst : ExpWord → ℕ
  | [] => 0
  | e :: w => 3 ^ w.length + 2 ^ e * affineConst w

/-- アフィン定数を整数へ持ち上げたもの。 -/
def affineConstInt (w : ExpWord) : ℤ := affineConst w

/-- `3^p - 2^H`。centerとdeterminantで使用する。 -/
def determinant (w : ExpWord) : ℤ :=
  (3 : ℤ) ^ oddSteps w - (2 : ℤ) ^ twoSteps w

/-- 語 `w` が自然数 `x` を自然数 `y` へ送るアフィン等式。 -/
def Realizes (w : ExpWord) (x y : ℕ) : Prop :=
  2 ^ twoSteps w * y = 3 ^ oddSteps w * x + affineConst w

/-- `Y = X + 2^«λ» u` かつ `u` が奇数であるという2進return分解。 -/
def IsReturn (X Y «λ» u : ℕ) : Prop :=
  Y = X + 2 ^ «λ» * u ∧ Odd u

/-- 語に対応する臨界差の整数版 `3^p - 2^H` の符号判定。 -/
def Expanding (w : ExpWord) : Prop :=
  2 ^ twoSteps w < 3 ^ oddSteps w

/-- 語に対応する純乗法係数が1未満であること。 -/
def Contracting (w : ExpWord) : Prop :=
  3 ^ oddSteps w < 2 ^ twoSteps w

@[simp] lemma oddSteps_nil : oddSteps ([] : ExpWord) = 0 := rfl
@[simp] lemma twoSteps_nil : twoSteps ([] : ExpWord) = 0 := rfl
@[simp] lemma affineConst_nil : affineConst ([] : ExpWord) = 0 := rfl

@[simp] lemma oddSteps_cons (e : ℕ) (w : ExpWord) :
    oddSteps (e :: w) = oddSteps w + 1 := by
  simp [oddSteps]

@[simp] lemma twoSteps_cons (e : ℕ) (w : ExpWord) :
    twoSteps (e :: w) = e + twoSteps w := by
  simp [twoSteps]

@[simp] lemma affineConst_cons (e : ℕ) (w : ExpWord) :
    affineConst (e :: w) = 3 ^ oddSteps w + 2 ^ e * affineConst w := by
  rfl

lemma oddSteps_append (u v : ExpWord) :
    oddSteps (u ++ v) = oddSteps u + oddSteps v := by
  simp [oddSteps]

lemma twoSteps_append (u v : ExpWord) :
    twoSteps (u ++ v) = twoSteps u + twoSteps v := by
  simp [twoSteps]

/-- アフィン定数の連結公式。 -/
theorem affineConst_append (u v : ExpWord) :
    affineConst (u ++ v) =
      3 ^ oddSteps v * affineConst u +
      2 ^ twoSteps u * affineConst v := by
  induction u with
  | nil =>
      simp [affineConst, oddSteps, twoSteps]
  | cons e u ih =>
      simp only [List.cons_append, affineConst_cons, oddSteps_append,
         twoSteps_cons, ih]
      rw [pow_add, pow_add]
      ring

/-- determinantの連結公式。 -/
theorem determinant_append (u v : ExpWord) :
    determinant (u ++ v) =
      (3 : ℤ) ^ oddSteps v * determinant u +
      (2 : ℤ) ^ twoSteps u * determinant v := by
  simp only [determinant, oddSteps_append, twoSteps_append]
  rw [pow_add, pow_add]
  ring

lemma valid_append {u v : ExpWord} (hu : Valid u) (hv : Valid v) : Valid (u ++ v) := by
  intro e he
  rw [List.mem_append] at he
  rcases he with he | he
  · exact hu e he
  · exact hv e he

lemma valid_prefix {u v : ExpWord} (h : Valid (u ++ v)) : Valid u := by
  intro e he
  exact h e (by simp [he])

/-- 正の指数語では、総2除算数は奇数操作数以上である。 -/
lemma oddSteps_le_twoSteps {w : ExpWord} (hw : Valid w) :
    oddSteps w ≤ twoSteps w := by
  induction w with
  | nil => simp [oddSteps, twoSteps]
  | cons e w ih =>
      have he : 0 < e := hw e (by simp)
      have hw' : Valid w := by
        intro a ha
        exact hw a (by simp [ha])
      have hi := ih hw'
      simp only [oddSteps_cons, twoSteps_cons]
      omega

/-- 正の指数を持つ非空語では、総2除算数は正である。 -/
lemma twoSteps_pos_of_valid_nonempty {w : ExpWord}
    (hw : Valid w) (hne : w ≠ []) : 0 < twoSteps w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      have he : 0 < e := hw e (by simp)
      simp only [twoSteps_cons]
      omega

end ExpWord

end CollatzFirstLayer
