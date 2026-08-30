import CollatzLean.Collatz2.RecordFerrers.NormalForm.UniversalFixedFiberNormalForm
import CollatzLean.Collatz2.Matrix.Representation
import Mathlib.Tactic.FinCases

/-!
# Universal excess の上三角行列表現

`UniversalFixedFiberNormalForm` の項目 8 を Matrix 層へ分離する。
NormalForm の正本を matrix に依存させず、従来の `AffineTransfer` representation を
corollary として与えるための薄い bridge である。
-/

namespace Collatz2
namespace RecordFerrers
namespace UniversalMatrix

open Word
open scoped Matrix

/-- fixed `(p,H)` の universal bottom matrix。 -/
def universalBottomMatrix (p H : ℕ) : MatrixAnalysis.TransferMatrix :=
  !![((3 ^ p : ℕ) : ℤ), ((3 ^ p - 2 ^ p : ℕ) : ℤ);
     0,                    ((2 ^ H : ℕ) : ℤ)]

/-- universal excess を upper-right nilpotent direction だけに置く matrix。 -/
def universalExcessMatrix (E : ℕ) : MatrixAnalysis.TransferMatrix :=
  !![0, (E : ℤ);
     0, 0]

/--
## 8. Universal upper-triangular normal form

任意 fixed-fiber point の upper-triangular representation は

  M(x) = M_bottom(p,H) + E(x) e₁₂

に exact 分解する。

従って fixed `(A,C)=(2^H,3^p)` 内の可変情報は upper-right の `E` 一個だけに集まる。
-/
theorem representation_ofWord_eq_universalBottom_add_excess
    {p H : ℕ}
    (x : FiberPoint p H) :
    MatrixAnalysis.representation (AffineTransfer.ofWord x.word) =
      universalBottomMatrix p H +
        universalExcessMatrix (universalExcess x) := by
  have hB := affineConst_eq_baseline_add_universalExcess x
  ext i j
  fin_cases i <;> fin_cases j
  · simp [MatrixAnalysis.representation, AffineTransfer.ofWord,
      universalBottomMatrix, universalExcessMatrix,
      x.oddSteps_eq]
  · change
      (affineConst x.word : ℤ) =
        ((3 ^ p - 2 ^ p : ℕ) : ℤ) +
          (universalExcess x : ℤ)
    exact_mod_cast hB
  · simp [MatrixAnalysis.representation, AffineTransfer.ofWord,
      universalBottomMatrix, universalExcessMatrix]
  · simp [MatrixAnalysis.representation, AffineTransfer.ofWord,
      universalBottomMatrix, universalExcessMatrix,
      x.twoSteps_eq]

end UniversalMatrix
end RecordFerrers
end Collatz2
