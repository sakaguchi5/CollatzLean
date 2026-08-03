import CollatzLean.CollatzFirstLayer.Affine
import Mathlib.Tactic.FieldSimp
/-!
# centerとdeterminant

語のアフィン写像に付随するcenterと、二語間の交差行列式を定義する。
符号を失わないため、determinantは整数、centerは有理数で扱う。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- determinantが0でない語の有理center。 -/
def center (w : ExpWord) : ℚ :=
  (affineConstInt w : ℚ) / (determinant w : ℚ)

/-- 二語のcenter差を測る交差行列式。 -/
def omega (u v : ExpWord) : ℤ :=
  affineConstInt u * determinant v -
  affineConstInt v * determinant u

@[simp] lemma omega_self (w : ExpWord) : omega w w = 0 := by
  simp [omega]

lemma omega_skew (u v : ExpWord) : omega v u = -omega u v := by
  simp [omega]

/-- center差をomegaで表す公式。 -/
theorem center_difference_formula {u v : ExpWord}
    (hu : determinant u ≠ 0) (hv : determinant v ≠ 0) :
    center u - center v =
      (omega u v : ℚ) /
        ((determinant u : ℚ) * (determinant v : ℚ)) := by
  have huq : (determinant u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hvq : (determinant v : ℚ) ≠ 0 := by exact_mod_cast hv
  unfold center omega
  push_cast
  field_simp [huq, hvq]

/-- 右側へ語を連結したときのomegaの局所化公式。 -/
theorem omega_append_right (u v : ExpWord) :
    omega u (u ++ v) =
      (2 : ℤ) ^ twoSteps u * omega u v := by
  unfold omega affineConstInt
  rw [determinant_append, affineConst_append]
  push_cast
  ring

end ExpWord
end CollatzFirstLayer
