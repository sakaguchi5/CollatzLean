import CollatzLean.Collatz.Word.Geometry

/-!
# contracting語の合成

finite word geometryで繰り返し使うcontracting語の連結閉性を独立させる。
-/

namespace Collatz
namespace Word

/-- contracting語どうしの連結もcontracting。 -/
theorem Contracting.append
    {u v : Collatz.Word}
    (hu : u.Contracting) (hv : v.Contracting) :
    (u ++ v).Contracting := by
  unfold Contracting at hu hv ⊢
  rw [oddSteps_append, twoSteps_append, pow_add, pow_add]
  have hv3 : 0 < 3 ^ v.oddSteps := Nat.pow_pos (by omega)
  have hu2 : 0 < 2 ^ u.twoSteps := Nat.pow_pos (by omega)
  have h₁ :
      3 ^ u.oddSteps * 3 ^ v.oddSteps <
        2 ^ u.twoSteps * 3 ^ v.oddSteps :=
    (Nat.mul_lt_mul_right hv3).2 hu
  have h₂ :
      2 ^ u.twoSteps * 3 ^ v.oddSteps <
        2 ^ u.twoSteps * 2 ^ v.twoSteps :=
    (Nat.mul_lt_mul_left hu2).2 hv
  exact lt_trans h₁ h₂

end Word
end Collatz
