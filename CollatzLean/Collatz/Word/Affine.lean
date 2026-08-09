import CollatzLean.Collatz.Word.Basic
import Mathlib.Tactic.LinearCombination

/-!
# 有限語のアフィン計算
-/

namespace Collatz
namespace Word

/-- 空語の実現。 -/
theorem realizes_nil (x : ℕ) : Realizes ([] : Collatz.Word) x x := by
  simp [Realizes, oddSteps, twoSteps, affineConst]

/-- 1文字語の実現。 -/
theorem realizes_singleton_iff (e x y : ℕ) :
    Realizes ([e] : Collatz.Word) x y ↔ 2 ^ e * y = 3 * x + 1 := by
  simp [Realizes, oddSteps, twoSteps, affineConst]

/-- 二つの有限実現を連結する。 -/
theorem Realizes.append {u v : Collatz.Word} {x y z : ℕ}
    (hu : u.Realizes x y) (hv : v.Realizes y z) :
    (u ++ v).Realizes x z := by
  unfold Realizes at hu hv ⊢
  rw [twoSteps_append, oddSteps_append, affineConst_append, pow_add, pow_add]
  calc
    (2 ^ u.twoSteps * 2 ^ v.twoSteps) * z
        = 2 ^ u.twoSteps * (2 ^ v.twoSteps * z) := by ring
    _ = 2 ^ u.twoSteps * (3 ^ v.oddSteps * y + v.affineConst) := by rw [hv]
    _ = 3 ^ v.oddSteps * (2 ^ u.twoSteps * y) + 2 ^ u.twoSteps * v.affineConst := by ring
    _ = 3 ^ v.oddSteps * (3 ^ u.oddSteps * x + u.affineConst) +
          2 ^ u.twoSteps * v.affineConst := by rw [hu]
    _ = (3 ^ u.oddSteps * 3 ^ v.oddSteps) * x +
          (3 ^ v.oddSteps * u.affineConst + 2 ^ u.twoSteps * v.affineConst) := by ring

/-- 自然数実現を整数実現へ持ち上げる。 -/
theorem Realizes.toInt {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) : w.RealizesInt x y := by
  unfold Realizes at h
  unfold RealizesInt affineConstInt
  exact_mod_cast h

/-- 実現式のdefect恒等式。 -/
theorem Realizes.defect {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) :
    w.affineConstInt + w.determinant * (x : ℤ) =
      (2 : ℤ) ^ w.twoSteps * ((y : ℤ) - x) := by
  have hz := h.toInt
  unfold RealizesInt at hz
  unfold determinant
  linear_combination -hz

/-- return分解を代入したdefect恒等式。 -/
theorem Realizes.return_defect
    {w : Collatz.Word} {X Y lambda u : ℕ}
    (hw : w.Realizes X Y) (hr : IsReturn X Y lambda u) :
    w.affineConstInt + w.determinant * (X : ℤ) =
      (2 : ℤ) ^ (w.twoSteps + lambda) * (u : ℤ) := by
  rcases hr with ⟨rfl, _⟩
  have h := hw.defect
  have hdiff :
      ((X + 2 ^ lambda * u : ℕ) : ℤ) - (X : ℤ) =
        (2 : ℤ) ^ lambda * (u : ℤ) := by
    push_cast
    ring
  rw [hdiff] at h
  simpa [pow_add, mul_assoc] using h

/-- 終点から見た符号付きendpoint defect。 -/
def endpointDefect (w : Collatz.Word) (y : ℤ) : ℤ :=
  -w.determinant * y - w.affineConstInt

/-- endpoint defectは開始・終了差をexactに記録する。 -/
theorem Realizes.endpointDefect_eq
    {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) :
    w.endpointDefect y =
      (3 : ℤ) ^ w.oddSteps * ((x : ℤ) - y) := by
  have hz := h.toInt
  unfold RealizesInt at hz
  unfold endpointDefect determinant
  calc
    -(3 ^ w.oddSteps - 2 ^ w.twoSteps) * (y : ℤ) -
        w.affineConstInt
        =
      2 ^ w.twoSteps * (y : ℤ) -
        3 ^ w.oddSteps * (y : ℤ) -
        w.affineConstInt := by
          ring
    _ =
      (3 ^ w.oddSteps * (x : ℤ) + w.affineConstInt) -
        3 ^ w.oddSteps * (y : ℤ) -
        w.affineConstInt := by
          rw [hz]
    _ =
      3 ^ w.oddSteps * ((x : ℤ) - y) := by
          ring

/-- 整数実現の平行移動。 -/
theorem RealizesInt.translate
    {w : Collatz.Word} {x y k : ℤ}
    (h : w.RealizesInt x y) :
    w.RealizesInt
      (x + (2 : ℤ) ^ w.twoSteps * k)
      (y + (3 : ℤ) ^ w.oddSteps * k) := by
  unfold RealizesInt at h ⊢
  linear_combination h

end Word
end Collatz
