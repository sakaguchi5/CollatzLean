import CollatzLean.Collatz.Word.Affine

/-!
# centerと交差核
-/

namespace Collatz
namespace Word

/-- determinantが0でない語に付随する有理center。 -/
def center (w : Collatz.Word) : ℚ :=
  (w.affineConstInt : ℚ) / (w.determinant : ℚ)

/-- 二語のcenter差を測る交差行列式。 -/
def omega (u v : Collatz.Word) : ℤ :=
  u.affineConstInt * v.determinant -
    v.affineConstInt * u.determinant

@[simp] theorem omega_self (w : Collatz.Word) : w.omega w = 0 := by
  simp [omega]

/-- omegaは反対称。 -/
theorem omega_skew (u v : Collatz.Word) : v.omega u = -u.omega v := by
  simp [omega]

/-- center差をomegaで表す。 -/
theorem center_difference
    {u v : Collatz.Word}
    (hu : u.determinant ≠ 0) (hv : v.determinant ≠ 0) :
    u.center - v.center =
      (u.omega v : ℚ) /
        ((u.determinant : ℚ) * (v.determinant : ℚ)) := by
  have huq : (u.determinant : ℚ) ≠ 0 := by
    exact_mod_cast hu
  have hvq : (v.determinant : ℚ) ≠ 0 := by
    exact_mod_cast hv
  unfold center omega
  push_cast
  rw [eq_div_iff (mul_ne_zero huq hvq)]
  ring_nf
  simp [huq, hvq]

/-- 右へ語を連結したときのomega。 -/
theorem omega_append_right (u v : Collatz.Word) :
    u.omega (u ++ v) = (2 : ℤ) ^ u.twoSteps * u.omega v := by
  unfold omega affineConstInt
  rw [determinant_append, affineConst_append]
  push_cast
  ring

end Word
end Collatz
