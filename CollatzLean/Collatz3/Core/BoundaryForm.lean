import CollatzLean.Collatz2.Core.BoundaryForm

/-!
# Collatz3 compatibility wrapper

`BoundaryForm` の正本は `Collatz2.Core.BoundaryForm` へ移動した。
このファイルは既存 `Collatz3.*` API を壊さないための薄い wrapper。
-/

namespace Collatz3

namespace AffineTransfer

abbrev boundaryForm
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) : ℤ :=
  Collatz2.AffineTransfer.boundaryForm T x y

abbrev diagonalBoundaryForm
    (T : Collatz2.AffineTransfer)
    (x : ℕ) : ℤ :=
  Collatz2.AffineTransfer.diagonalBoundaryForm T x

abbrev contractionGap
    (T : Collatz2.AffineTransfer) : ℕ :=
  Collatz2.AffineTransfer.contractionGap T

abbrev contractionCompensation
    (T : Collatz2.AffineTransfer)
    (x : ℕ) : ℕ :=
  Collatz2.AffineTransfer.contractionCompensation T x

abbrev positiveReturnCost
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) : ℕ :=
  Collatz2.AffineTransfer.positiveReturnCost T x y

theorem realizes_iff_boundaryForm_eq_zero
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) :
    T.Realizes x y ↔ boundaryForm T x y = 0 :=
  Collatz2.AffineTransfer.realizes_iff_boundaryForm_eq_zero T x y

theorem boundaryForm_followedBy
    (T U : Collatz2.AffineTransfer)
    (x y z : ℕ) :
    boundaryForm (T.followedBy U) x z =
      (U.oddCoeff : ℤ) * boundaryForm T x y +
        (T.twoCoeff : ℤ) * boundaryForm U y z :=
  Collatz2.AffineTransfer.boundaryForm_followedBy T U x y z

theorem translate_eq_contractionCompensation_add_positiveReturnCost
    {T : Collatz2.AffineTransfer}
    {x y : ℕ}
    (hRealizes : T.Realizes x y)
    (hContracting : T.oddCoeff ≤ T.twoCoeff)
    (hReturn : x ≤ y) :
    T.translate =
      contractionCompensation T x + positiveReturnCost T x y :=
  Collatz2.AffineTransfer.translate_eq_contractionCompensation_add_positiveReturnCost
    hRealizes hContracting hReturn

end AffineTransfer
end Collatz3
