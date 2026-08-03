import CollatzLean.CollatzFirstLayer.Basic
import Mathlib.Tactic.LinearCombination
/-!
# アフィン実現と語の合成

有限指数語を実際の自然数間のアフィン等式として扱う。
自然数除算を定義の中心に置かず、整式等式だけで証明する。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 空語は各自然数を自分自身へ送る。 -/
lemma realizes_nil (x : ℕ) : Realizes [] x x := by
  simp [Realizes, oddSteps, twoSteps, affineConst]

/-- 1文字語の実現式。 -/
lemma realizes_singleton_iff (e x y : ℕ) :
    Realizes [e] x y ↔ 2 ^ e * y = 3 * x + 1 := by
  simp [Realizes, oddSteps, twoSteps, affineConst]

/--
前半語と後半語の実現を合成すると、連結語の実現が得られる。
-/
theorem realizes_append {u v : ExpWord} {x y z : ℕ}
    (hu : Realizes u x y) (hv : Realizes v y z) :
    Realizes (u ++ v) x z := by
  unfold Realizes at hu hv ⊢
  rw [twoSteps_append, oddSteps_append, affineConst_append, pow_add, pow_add]
  calc
    (2 ^ twoSteps u * 2 ^ twoSteps v) * z
        = 2 ^ twoSteps u * (2 ^ twoSteps v * z) := by ring
    _ = 2 ^ twoSteps u *
          (3 ^ oddSteps v * y + affineConst v) := by rw [hv]
    _ = 3 ^ oddSteps v * (2 ^ twoSteps u * y) +
          2 ^ twoSteps u * affineConst v := by ring
    _ = 3 ^ oddSteps v *
          (3 ^ oddSteps u * x + affineConst u) +
          2 ^ twoSteps u * affineConst v := by rw [hu]
    _ = (3 ^ oddSteps u * 3 ^ oddSteps v) * x +
          (3 ^ oddSteps v * affineConst u +
           2 ^ twoSteps u * affineConst v) := by ring

/--
実現式から得られる基本defect恒等式。
`y = x + 2^«λ»u` を代入する前の形である。
-/
lemma realizes_defect_identity {w : ExpWord} {x y : ℕ}
    (h : Realizes w x y) :
    affineConstInt w + determinant w * (x : ℤ) =
      (2 : ℤ) ^ twoSteps w * ((y : ℤ) - x) := by
  unfold Realizes at h
  have hz :
      (2 : ℤ) ^ twoSteps w * (y : ℤ) =
        (3 : ℤ) ^ oddSteps w * (x : ℤ) + (affineConst w : ℤ) := by
    exact_mod_cast h
  unfold affineConstInt determinant
  linear_combination -hz

/-- return分解を代入したdefect恒等式。 -/
theorem realizes_return_defect {w : ExpWord} {X Y «λ» u : ℕ}
    (hw : Realizes w X Y) (hr : IsReturn X Y «λ» u) :
    affineConstInt w + determinant w * (X : ℤ) =
      (2 : ℤ) ^ (twoSteps w + «λ») * (u : ℤ) := by
  rcases hr with ⟨rfl, hu⟩
  have h := realizes_defect_identity hw
  have hdiff :
      ((X + 2 ^ «λ» * u : ℕ) : ℤ) - (X : ℤ) =
        (2 : ℤ) ^ «λ» * (u : ℤ) := by
    push_cast
    ring
  rw [hdiff] at h
  rw [pow_add]
  simpa [mul_assoc] using h

end ExpWord
end CollatzFirstLayer
