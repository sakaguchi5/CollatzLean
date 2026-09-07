import CollatzLean.Collatz3.Core.Word
import CollatzLean.Collatz3.Core.AffineTransfer
import Mathlib.Tactic.Ring

/-!
# Collatz3: exponent word から affine transfer への唯一の写像

`affineConst` を別の再帰正本として持たない。
1 文字 transfer の composition の `translate` を唯一の translation とする。
-/

namespace Collatz3
namespace Word

/-- 1 文字指数 `e` の transfer: `2^e * y = 3 * x + 1`。 -/
def stepTransfer (e : ℕ) : AffineTransfer :=
  { oddCoeff := 3
    twoCoeff := 2 ^ e
    translate := 1 }

/-- exponent word 全体の affine transfer。 -/
def transfer : Word → AffineTransfer
  | [] => AffineTransfer.id
  | e :: w => (stepTransfer e).followedBy (transfer w)

@[simp] theorem transfer_nil :
    transfer ([] : Word) = AffineTransfer.id := rfl

@[simp] theorem transfer_cons (e : ℕ) (w : Word) :
    transfer (e :: w) = (stepTransfer e).followedBy (transfer w) := rfl

/-- word append は transfer composition に exact に一致する。 -/
theorem transfer_append (u v : Word) :
    transfer (u ++ v) = (transfer u).followedBy (transfer v) := by
  induction u with
  | nil =>
      simp [transfer]
  | cons e u ih =>
      simp [transfer, ih, AffineTransfer.followedBy_assoc]

/-- word transfer の 3 側係数。 -/
@[simp] theorem transfer_oddCoeff (w : Word) :
    (transfer w).oddCoeff = 3 ^ oddSteps w := by
  induction w with
  | nil =>
      simp [transfer, oddSteps]
  | cons e w ih =>
      simp [transfer, stepTransfer, ih, oddSteps, pow_succ, Nat.mul_comm]

/-- word transfer の 2 側係数。 -/
@[simp] theorem transfer_twoCoeff (w : Word) :
    (transfer w).twoCoeff = 2 ^ twoSteps w := by
  induction w with
  | nil =>
      simp [transfer, twoSteps]
  | cons e w ih =>
      simp [transfer, stepTransfer, ih, twoSteps, pow_add]

/-- word の affine translation。正本は `transfer.translate`。 -/
def affineConst (w : Word) : ℕ :=
  (transfer w).translate

@[simp] theorem affineConst_nil : affineConst ([] : Word) = 0 := by
  rfl

/-- 旧来の再帰公式は transfer composition から導く。 -/
@[simp] theorem affineConst_cons (e : ℕ) (w : Word) :
    affineConst (e :: w) =
      3 ^ oddSteps w + 2 ^ e * affineConst w := by
  simp [affineConst, transfer, stepTransfer]

/-- affine translation の連結公式。 -/
theorem affineConst_append (u v : Word) :
    affineConst (u ++ v) =
      3 ^ oddSteps v * affineConst u +
        2 ^ twoSteps u * affineConst v := by
  simp [affineConst, transfer_append]

/-- word の signed scale gap `2^H - 3^p`。 -/
def signedScaleGap (w : Word) : ℤ :=
  (transfer w).signedScaleGap

@[simp] theorem signedScaleGap_eq (w : Word) :
    signedScaleGap w =
      (2 ^ twoSteps w : ℤ) - (3 ^ oddSteps w : ℤ) := by
  simp [signedScaleGap, AffineTransfer.signedScaleGap, Arithmetic.delta]

end Word
end Collatz3
