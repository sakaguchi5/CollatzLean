import CollatzLean.Collatz2.Core.Realization
import Mathlib.Tactic.Linarith

/-!
# Collatz3: source-target boundary form

`Collatz3` は `Collatz2` を import して、新しい統一座標系を最短距離で検証する
研究層である。

有限 affine transfer

  A * y = C * x + B

に対し、source / target を別々に動かす二変数形式

  Θ_T(X,Y) = B + C*X - A*Y

を導入する。actual realization は `Θ_T(x,y)=0` そのものである。

さらに contracting positive return では

  B = (A-C)*x + A*(y-x)

を自然数上の exact equality として保持する。
-/

namespace Collatz3

open Collatz2

namespace AffineTransfer

/-- source / target を別々に持つ boundary form。 -/
def boundaryForm
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) : ℤ :=
  (T.translate : ℤ) +
    (T.oddCoeff : ℤ) * (x : ℤ) -
    (T.twoCoeff : ℤ) * (y : ℤ)

/-- actual realization は boundary form の zero-locus。 -/
theorem realizes_iff_boundaryForm_eq_zero
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) :
    T.Realizes x y ↔ boundaryForm T x y = 0 := by
  constructor
  · intro h
    unfold Collatz2.AffineTransfer.Realizes at h
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
    unfold Collatz2.AffineTransfer.Realizes
    exact_mod_cast hZ

/-- diagonal restriction は通常の same-frame displacement。 -/
def diagonalBoundaryForm
    (T : Collatz2.AffineTransfer)
    (x : ℕ) : ℤ :=
  boundaryForm T x x

/-- contracting coefficient gap `A-C`。 -/
def contractionGap
    (T : Collatz2.AffineTransfer) : ℕ :=
  T.twoCoeff - T.oddCoeff

/-- actual source height に対する contraction compensation。 -/
def contractionCompensation
    (T : Collatz2.AffineTransfer)
    (x : ℕ) : ℕ :=
  contractionGap T * x

/-- actual frame が右へ移動するための cost。 -/
def positiveReturnCost
    (T : Collatz2.AffineTransfer)
    (x y : ℕ) : ℕ :=
  T.twoCoeff * (y - x)

/--
contracting realization の translation は

  B = contraction compensation + actual positive-return cost

へ exact に分解される。
-/
theorem translate_eq_contractionCompensation_add_positiveReturnCost
    {T : Collatz2.AffineTransfer}
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
      T.twoCoeff * y = T.oddCoeff * x + T.translate := by
    exact hRealizes
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
end Collatz3
