import CollatzLean.Collatz2.Core.DisplacementForm
import Mathlib.Tactic.Positivity
/-!
# Collatz2: genuine word translation path

任意の affine transfer では `B` は自由だが、genuine Collatz word では
`B = Word.affineConst w` に固定される。

append law

  `B(u ++ v) = 3^|v| B(u) + 2^H(u) B(v)`

を translation cocycle として読み、exact equality より薄い Archimedean shadow

  `B(w) < 2^H(w) * 3^p(w)`

も取り出す。
-/

namespace Collatz2
namespace Word

/-- Semantic name for the exact translation cocycle under word concatenation. -/
theorem translationCocycle_append (u v : Word) :
    affineConst (u ++ v) =
      3 ^ oddSteps v * affineConst u +
        2 ^ twoSteps u * affineConst v :=
  affineConst_append u v

/--
Every genuine word translation is strictly smaller than the product of its two
diagonal coefficients.
-/
theorem affineConst_lt_twoPow_mul_threePow (w : Word) :
    affineConst w <
      2 ^ twoSteps w * 3 ^ oddSteps w := by
  induction w with
  | nil =>
      simp [affineConst, twoSteps, oddSteps]
  | cons e w ih =>
      let X := 2 ^ e
      let Y := 2 ^ twoSteps w
      let Z := 3 ^ oddSteps w
      have hXpos : 0 < X := by
        dsimp [X]
        positivity
      have hYpos : 0 < Y := by
        dsimp [Y]
        positivity
      have hZpos : 0 < Z := by
        dsimp [Z]
        positivity
      have hscaled : X * affineConst w < X * (Y * Z) := by
        exact Nat.mul_lt_mul_of_pos_left (by simpa [Y, Z] using ih) hXpos
      have hXYpos : 0 < X * Y := Nat.mul_pos hXpos hYpos
      have hXYone : 1 ≤ X * Y := by omega
      have hZle : Z ≤ (X * Y) * Z := by
        have h := Nat.mul_le_mul_right Z hXYone
        simpa using h
      have hQpos : 0 < (X * Y) * Z := Nat.mul_pos hXYpos hZpos
      have hstep :
          Z + X * affineConst w < 3 * ((X * Y) * Z) := by
        have h1 :
            Z + X * affineConst w < Z + (X * Y) * Z := by
          have hs : X * affineConst w < (X * Y) * Z := by
            simpa [mul_assoc] using hscaled
          exact Nat.add_lt_add_left hs Z
        omega
      simp only [affineConst_cons, twoSteps_cons, oddSteps_cons]
      rw [pow_add, pow_succ]
      change Z + X * affineConst w < (X * Y) * (Z * 3)
      calc
        Z + X * affineConst w < 3 * ((X * Y) * Z) := hstep
        _ = (X * Y) * (Z * 3) := by ring

/-- Transfer-level version of the genuine translation size bound. -/
theorem ofWord_translate_lt_diagonal_product (w : Word) :
    (AffineTransfer.ofWord w).translate <
      (AffineTransfer.ofWord w).twoCoeff *
        (AffineTransfer.ofWord w).oddCoeff := by
  simpa [AffineTransfer.ofWord] using
    affineConst_lt_twoPow_mul_threePow w

/-- The constant term of the word displacement form satisfies the same bound. -/
theorem displacementForm_constant_lt_diagonal_product (w : Word) :
    (AffineTransfer.ofWord w).displacementForm.constant <
      ((AffineTransfer.ofWord w).twoCoeff *
        (AffineTransfer.ofWord w).oddCoeff : ℕ) := by
  change (Word.affineConst w : ℤ) <
    (((2 ^ twoSteps w) * (3 ^ oddSteps w) : ℕ) : ℤ)
  exact_mod_cast affineConst_lt_twoPow_mul_threePow w

end Word
end Collatz2
