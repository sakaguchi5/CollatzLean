import CollatzLean.Collatz2.Core.Realization
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Core: source-target boundary form

任意の有限 affine transfer

  A * y = C * x + B

に対し、source / target を別々に持つ二変数形式

  Θ_T(X,Y) = B + C*X - A*Y

を導入する。actual realization は `Θ_T(x,y)=0` そのものである。
この座標は current A に依存しないため Collatz2 の一般層に置く。
-/

namespace Collatz2
namespace AffineTransfer

/-- source / target を別々に持つ boundary form。 -/
def boundaryForm
    (T : AffineTransfer)
    (x y : ℕ) : ℤ :=
  (T.translate : ℤ) +
    (T.oddCoeff : ℤ) * (x : ℤ) -
    (T.twoCoeff : ℤ) * (y : ℤ)

/-- actual realization は boundary form の zero-locus。 -/
theorem realizes_iff_boundaryForm_eq_zero
    (T : AffineTransfer)
    (x y : ℕ) :
    T.Realizes x y ↔ boundaryForm T x y = 0 := by
  constructor
  · intro h
    unfold Realizes at h
    unfold boundaryForm
    have hZ :
        (T.twoCoeff : ℤ) * (y : ℤ) =
          (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) := by
      exact_mod_cast h
    linarith
  · intro h
    unfold boundaryForm at h
    have hZ :
        (T.twoCoeff : ℤ) * (y : ℤ) =
          (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) := by
      linarith
    unfold Realizes
    exact_mod_cast hZ

/-- diagonal restriction は same-frame displacement の boundary 版。 -/
def diagonalBoundaryForm
    (T : AffineTransfer)
    (x : ℕ) : ℤ :=
  boundaryForm T x x

/--
Boundary form の composition law。
中間 frame `y` は exact に消去される。
-/
theorem boundaryForm_followedBy
    (T U : AffineTransfer)
    (x y z : ℕ) :
    boundaryForm (T.followedBy U) x z =
      (U.oddCoeff : ℤ) * boundaryForm T x y +
        (T.twoCoeff : ℤ) * boundaryForm U y z := by
  unfold boundaryForm followedBy
  push_cast
  ring

/-- 二つの zero boundary は composition の zero boundary を与える。 -/
theorem boundaryForm_followedBy_eq_zero
    {T U : AffineTransfer}
    {x y z : ℕ}
    (hT : boundaryForm T x y = 0)
    (hU : boundaryForm U y z = 0) :
    boundaryForm (T.followedBy U) x z = 0 := by
  rw [boundaryForm_followedBy, hT, hU]
  ring

/-- contracting coefficient gap `A-C`。 -/
def contractionGap
    (T : AffineTransfer) : ℕ :=
  T.twoCoeff - T.oddCoeff

/-- actual source height に対する contraction compensation。 -/
def contractionCompensation
    (T : AffineTransfer)
    (x : ℕ) : ℕ :=
  contractionGap T * x

/-- actual frame が右へ移動するための cost。 -/
def positiveReturnCost
    (T : AffineTransfer)
    (x y : ℕ) : ℕ :=
  T.twoCoeff * (y - x)

/--
contracting realization の translation は

  B = (A-C)*x + A*(y-x)

へ exact に分解される。
-/
theorem translate_eq_contractionCompensation_add_positiveReturnCost
    {T : AffineTransfer}
    {x y : ℕ}
    (hRealizes : T.Realizes x y)
    (hContracting : T.oddCoeff ≤ T.twoCoeff)
    (hReturn : x ≤ y) :
    T.translate =
      contractionCompensation T x +
        positiveReturnCost T x y := by
  have hGap :
      contractionGap T + T.oddCoeff = T.twoCoeff := by
    unfold contractionGap
    exact Nat.sub_add_cancel hContracting
  have hReturnAdd : x + (y - x) = y := by
    omega
  have hRealizes' :
      T.twoCoeff * y = T.oddCoeff * x + T.translate := hRealizes
  have hEq :
      (contractionCompensation T x + positiveReturnCost T x y) +
          T.oddCoeff * x =
        T.translate + T.oddCoeff * x := by
    calc
      (contractionCompensation T x + positiveReturnCost T x y) +
            T.oddCoeff * x
          = (contractionGap T + T.oddCoeff) * x +
              T.twoCoeff * (y - x) := by
                simp only [contractionCompensation, positiveReturnCost]
                ring
      _ = T.twoCoeff * x + T.twoCoeff * (y - x) := by
            rw [hGap]
      _ = T.twoCoeff * (x + (y - x)) := by ring
      _ = T.twoCoeff * y := by rw [hReturnAdd]
      _ = T.oddCoeff * x + T.translate := hRealizes'
      _ = T.translate + T.oddCoeff * x := by ring
  exact (Nat.add_right_cancel hEq).symm

end AffineTransfer
end Collatz2
