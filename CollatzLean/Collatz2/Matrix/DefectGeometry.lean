import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Local.Defect

/-!
# Collatz2 Matrix: defect as oriented projective geometry

既存 start defect を再定義しない。
homogeneous affine point `(x,1)` とその matrix image の wedge が
既存 defect の符号を exact に測ることを示す。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- projective affine chart の homogeneous vector。 -/
abbrev HomPoint := Fin 2 → ℤ

/-- 自然数 `x` を homogeneous point `(x,1)` として埋め込む。 -/
def affinePoint (x : ℕ) : HomPoint :=
  ![(x : ℤ), 1]

/-- 2次元 vector の oriented wedge。 -/
def wedge (p q : HomPoint) : ℤ :=
  p 0 * q 1 - p 1 * q 0

/-- transfer matrix による homogeneous image。 -/
def imagePoint (T : AffineTransfer) (x : ℕ) : HomPoint :=
  representation T *ᵥ affinePoint x

/-- image は `(Cx+B, A)`。 -/
theorem imagePoint_eq
    (T : AffineTransfer)
    (x : ℕ) :
    imagePoint T x =
      ![(T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ),
        (T.twoCoeff : ℤ)] := by
  funext i
  fin_cases i <;>
    simp [imagePoint, affinePoint, representation,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

/--
既存 start defect は affine point と matrix image の oriented wedge の負号。
-/
theorem startDefect_eq_neg_wedge
    (T : AffineTransfer)
    (x : ℕ) :
    T.startDefect x = -wedge (affinePoint x) (imagePoint T x) := by
  rw [imagePoint_eq]
  simp [wedge, affinePoint, AffineTransfer.startDefect,
    AffineTransfer.determinant]
  ring

/-- positive start defect は matrix image が wedge の負側にあることと同値。 -/
theorem startDefect_pos_iff_wedge_neg
    (T : AffineTransfer)
    (x : ℕ) :
    0 < T.startDefect x ↔
      wedge (affinePoint x) (imagePoint T x) < 0 := by
  rw [startDefect_eq_neg_wedge]
  omega

end MatrixAnalysis
end Collatz2
