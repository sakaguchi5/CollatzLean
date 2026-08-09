import CollatzLean.Collatz.Word.Affine

/-!
# 有限語replay
-/

namespace Collatz
namespace Word

/-- 自然数実現の語全体replay。 -/
theorem Realizes.replay
    {w : Collatz.Word} {X Z k : ℕ}
    (h : w.Realizes X Z) :
    w.Realizes
      (X + 2 ^ (w.twoSteps + 1) * k)
      (Z + 2 * 3 ^ w.oddSteps * k) := by
  unfold Realizes at h ⊢
  rw [pow_add]
  norm_num
  calc
    2 ^ w.twoSteps * (Z + 2 * 3 ^ w.oddSteps * k)
        = 2 ^ w.twoSteps * Z +
          3 ^ w.oddSteps * (2 ^ w.twoSteps * 2 * k) := by ring
    _ = (3 ^ w.oddSteps * X + w.affineConst) +
          3 ^ w.oddSteps * (2 ^ w.twoSteps * 2 * k) := by rw [h]
    _ = 3 ^ w.oddSteps *
          (X + (2 ^ w.twoSteps * 2) * k) + w.affineConst := by ring

end Word
end Collatz
