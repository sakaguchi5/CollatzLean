import CollatzLean.Collatz3.Core.WordTransfer
import Mathlib.Tactic.Ring

/-!
# Collatz3: affine endpoint equation

ここで定義するのは区間端点の affine equation だけであり、
途中の各指数が actual Collatz step であることは意味しない。
actual semantics は `Semantics` 層で別に定義する。
-/

namespace Collatz3
namespace AffineTransfer

/-- transfer `T` の端点方程式。 -/
def EndpointEquation (T : AffineTransfer) (x y : ℕ) : Prop :=
  T.twoCoeff * y = T.oddCoeff * x + T.translate

@[simp] theorem endpointEquation_id (x y : ℕ) :
    id.EndpointEquation x y ↔ x = y := by
  simp [EndpointEquation, id, eq_comm]

/-- 中間点を共有する端点方程式は composition できる。 -/
theorem EndpointEquation.followedBy
    {T U : AffineTransfer}
    {x y z : ℕ}
    (hT : T.EndpointEquation x y)
    (hU : U.EndpointEquation y z) :
    (T.followedBy U).EndpointEquation x z := by
  unfold EndpointEquation at hT hU ⊢
  calc
    (T.twoCoeff * U.twoCoeff) * z
        = T.twoCoeff * (U.twoCoeff * z) := by ring
    _ = T.twoCoeff * (U.oddCoeff * y + U.translate) := by rw [hU]
    _ = U.oddCoeff * (T.twoCoeff * y) + T.twoCoeff * U.translate := by ring
    _ = U.oddCoeff * (T.oddCoeff * x + T.translate) +
          T.twoCoeff * U.translate := by rw [hT]
    _ = (T.oddCoeff * U.oddCoeff) * x +
          (U.oddCoeff * T.translate + T.twoCoeff * U.translate) := by ring

end AffineTransfer

namespace Word

/-- word が持つ affine endpoint equation。 -/
def EndpointEquation (w : Word) (x y : ℕ) : Prop :=
  (transfer w).EndpointEquation x y

/-- word endpoint equation の展開形。 -/
theorem endpointEquation_iff (w : Word) (x y : ℕ) :
    w.EndpointEquation x y ↔
      2 ^ twoSteps w * y =
        3 ^ oddSteps w * x + affineConst w := by
  simp [EndpointEquation, AffineTransfer.EndpointEquation, affineConst]

/-- 空語の endpoint equation。 -/
@[simp] theorem endpointEquation_nil (x y : ℕ) :
    EndpointEquation ([] : Word) x y ↔ x = y := by
  simp [EndpointEquation]

/-- 二つの word endpoint equation を連結する。 -/
theorem EndpointEquation.append
    {u v : Word}
    {x y z : ℕ}
    (hu : u.EndpointEquation x y)
    (hv : v.EndpointEquation y z) :
    (u ++ v).EndpointEquation x z := by
  unfold EndpointEquation at hu hv ⊢
  rw [transfer_append]
  exact hu.followedBy hv

end Word
end Collatz3
