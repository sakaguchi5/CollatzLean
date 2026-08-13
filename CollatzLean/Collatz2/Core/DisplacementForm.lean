import CollatzLean.Collatz2.Core.AffineTransfer
import Mathlib.Tactic.Ring

/-!
# Collatz2: displacement form

`AffineTransfer = (C,A,B)` は有限 transfer の lossless な正本として残す。
このファイルでは、`B` に依存する解析の共通 interface として

  `Δ_T(X) = B + (C-A) X`

という整数一次式 `DisplacementForm` を導入する。

* 定数項は translation `B`
* 傾きは signed diagonal gap `C-A`
* 評価値は defect
* projective root は finite center
* 二 form の resultant は center separation

composition では一次式全体が exact に transport される。
-/

namespace Collatz2

/-- Integer linear form `constant + slope * X`. -/
@[ext]
structure DisplacementForm where
  constant : ℤ
  slope : ℤ
deriving DecidableEq

namespace DisplacementForm

/-- Evaluate a displacement form at an integer point. -/
def eval (D : DisplacementForm) (x : ℤ) : ℤ :=
  D.constant + D.slope * x

/-- Weighted sum used by affine-transfer composition. -/
def combine
    (a : ℤ) (D : DisplacementForm)
    (b : ℤ) (E : DisplacementForm) : DisplacementForm :=
  { constant := a * D.constant + b * E.constant
    slope := a * D.slope + b * E.slope }

@[simp] theorem combine_constant
    (a : ℤ) (D : DisplacementForm)
    (b : ℤ) (E : DisplacementForm) :
    (combine a D b E).constant =
      a * D.constant + b * E.constant := rfl

@[simp] theorem combine_slope
    (a : ℤ) (D : DisplacementForm)
    (b : ℤ) (E : DisplacementForm) :
    (combine a D b E).slope =
      a * D.slope + b * E.slope := rfl

/-- Evaluation commutes with weighted combination. -/
theorem eval_combine
    (a : ℤ) (D : DisplacementForm)
    (b : ℤ) (E : DisplacementForm)
    (x : ℤ) :
    (combine a D b E).eval x =
      a * D.eval x + b * E.eval x := by
  simp [eval, combine]
  ring

/--
`x` is a root of the form modulo natural modulus `m`, kept division-free as an
integer divisibility witness.
-/
def IsRootMod (D : DisplacementForm) (m : ℕ) (x : ℤ) : Prop :=
  ∃ k : ℤ, D.eval x = (m : ℤ) * k

/-- Root-mod is exactly integer divisibility of the evaluation. -/
theorem isRootMod_iff_dvd
    (D : DisplacementForm) (m : ℕ) (x : ℤ) :
    D.IsRootMod m x ↔ (m : ℤ) ∣ D.eval x := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩

/-- Signed separation/resultant of two displacement forms. -/
def resultant (D E : DisplacementForm) : ℤ :=
  D.constant * E.slope - E.constant * D.slope

/-- Two forms have the same projective root, division-free. -/
def SameRoot (D E : DisplacementForm) : Prop :=
  D.constant * E.slope = E.constant * D.slope

/-- Same root is exactly zero resultant. -/
theorem sameRoot_iff_resultant_eq_zero
    (D E : DisplacementForm) :
    SameRoot D E ↔ resultant D E = 0 := by
  unfold SameRoot resultant
  exact sub_eq_zero.symm

@[simp] theorem resultant_self (D : DisplacementForm) :
    resultant D D = 0 := by
  simp [resultant]

/-- Resultant is antisymmetric. -/
theorem resultant_swap (D E : DisplacementForm) :
    resultant E D = -resultant D E := by
  unfold resultant
  ring

end DisplacementForm

namespace AffineTransfer

/--
The universal displacement form of `A*y = C*x+B`:

  `Δ_T(X) = B + (C-A)X`.
-/
def displacementForm (T : AffineTransfer) : DisplacementForm :=
  { constant := (T.translate : ℤ)
    slope := T.determinant }

@[simp] theorem displacementForm_constant (T : AffineTransfer) :
    T.displacementForm.constant = (T.translate : ℤ) := rfl

@[simp] theorem displacementForm_slope (T : AffineTransfer) :
    T.displacementForm.slope = T.determinant := rfl

/-- The translation `B` is the constant term of the displacement form. -/
theorem translate_eq_displacementForm_constant (T : AffineTransfer) :
    (T.translate : ℤ) = T.displacementForm.constant := rfl

/-- The signed diagonal gap is the slope of the displacement form. -/
theorem determinant_eq_displacementForm_slope (T : AffineTransfer) :
    T.determinant = T.displacementForm.slope := rfl

/--
Composition transports the entire displacement form:

`Δ_(T;U) = C_U * Δ_T + A_T * Δ_U`.
-/
theorem displacementForm_followedBy
    (T U : AffineTransfer) :
    (T.followedBy U).displacementForm =
      DisplacementForm.combine
        (U.oddCoeff : ℤ) T.displacementForm
        (T.twoCoeff : ℤ) U.displacementForm := by
  apply DisplacementForm.ext <;>
  simp only [
    displacementForm,
    followedBy,
    determinant,
    Nat.cast_add,
    Nat.cast_mul,
    DisplacementForm.combine
  ]
  ring_nf

/-- Same-point evaluation form of the composition law. -/
theorem displacementForm_eval_followedBy
    (T U : AffineTransfer)
    (x : ℤ) :
    (T.followedBy U).displacementForm.eval x =
      (U.oddCoeff : ℤ) * T.displacementForm.eval x +
        (T.twoCoeff : ℤ) * U.displacementForm.eval x := by
  rw [displacementForm_followedBy]
  exact DisplacementForm.eval_combine _ _ _ _ _

/--
Signed projective separation of two affine transfers.
This is the high-level scalar whose matrix shadow was previously called `omega`.
-/
def separation (T U : AffineTransfer) : ℤ :=
  DisplacementForm.resultant T.displacementForm U.displacementForm

/-- Coefficient expansion of separation. -/
theorem separation_eq
    (T U : AffineTransfer) :
    T.separation U =
      (T.translate : ℤ) * U.determinant -
        (U.translate : ℤ) * T.determinant := by
  rfl

/-- Same projective center/root is exactly zero separation. -/
theorem sameDisplacementRoot_iff_separation_eq_zero
    (T U : AffineTransfer) :
    DisplacementForm.SameRoot T.displacementForm U.displacementForm ↔
      T.separation U = 0 := by
  exact DisplacementForm.sameRoot_iff_resultant_eq_zero _ _

/-- Separation is antisymmetric. -/
theorem separation_swap (T U : AffineTransfer) :
    U.separation T = -T.separation U := by
  exact DisplacementForm.resultant_swap _ _

/--
Separation from `T` to the composite scales by the prefix two-coefficient.
-/
theorem separation_left_followedBy
    (T U : AffineTransfer) :
    T.separation (T.followedBy U) =
      (T.twoCoeff : ℤ) * T.separation U := by
  simp [
    separation,
    displacementForm_followedBy,
    DisplacementForm.resultant,
    DisplacementForm.combine
  ]
  ring_nf

/--
Separation from the composite to `U` scales by the suffix odd-coefficient.
-/
theorem separation_followedBy_right
    (T U : AffineTransfer) :
    (T.followedBy U).separation U =
      (U.oddCoeff : ℤ) * T.separation U := by
  simp [
    separation,
    displacementForm_followedBy,
    DisplacementForm.resultant,
    DisplacementForm.combine
  ]
  ring_nf

end AffineTransfer
end Collatz2
