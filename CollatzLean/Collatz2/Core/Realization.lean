import CollatzLean.Collatz2.Core.AffineTransfer

/-!
# Collatz2: realization

Affine transfer と actual start/end の関係を独立に定義する。
ここではまだ符号分類や canonical representative は導入しない。
-/

namespace Collatz2

namespace AffineTransfer

/-- transfer `T` が自然数 `x -> y` を実現する。 -/
def Realizes (T : AffineTransfer) (x y : ℕ) : Prop :=
  T.twoCoeff * y = T.oddCoeff * x + T.translate

@[simp] theorem realizes_id (x y : ℕ) :
    id.Realizes x y ↔ x = y := by
  simp [Realizes, id,eq_comm]

/-- realization は transfer composition で連結できる。 -/
theorem Realizes.followedBy
    {T U : AffineTransfer}
    {x y z : ℕ}
    (hT : T.Realizes x y)
    (hU : U.Realizes y z) :
    (T.followedBy U).Realizes x z := by
  unfold Realizes at hT hU ⊢
  calc
    (T.twoCoeff * U.twoCoeff) * z
        = T.twoCoeff * (U.twoCoeff * z) := by ring
    _ = T.twoCoeff * (U.oddCoeff * y + U.translate) := by rw [hU]
    _ = U.oddCoeff * (T.twoCoeff * y) +
          T.twoCoeff * U.translate := by ring
    _ = U.oddCoeff * (T.oddCoeff * x + T.translate) +
          T.twoCoeff * U.translate := by rw [hT]
    _ = (T.oddCoeff * U.oddCoeff) * x +
          (U.oddCoeff * T.translate + T.twoCoeff * U.translate) := by ring

end AffineTransfer

namespace Word

/-- word の actual realization。 -/
def Realizes (w : Word) (x y : ℕ) : Prop :=
  (AffineTransfer.ofWord w).Realizes x y

/-- 空語は恒等 realization。 -/
theorem realizes_nil (x : ℕ) :
    Realizes ([] : Word) x x := by
  simp [Realizes]

/-- 1文字語の realization。 -/
theorem realizes_singleton_iff (e x y : ℕ) :
    Realizes ([e] : Word) x y ↔
      2 ^ e * y = 3 * x + 1 := by
  simp [Realizes, AffineTransfer.Realizes,
    AffineTransfer.ofWord, affineConst]

/-- 二つの word realization を連結する。 -/
theorem Realizes.append
    {u v : Word}
    {x y z : ℕ}
    (hu : Realizes u x y)
    (hv : Realizes v y z) :
    Realizes (u ++ v) x z := by
  unfold Realizes at hu hv ⊢
  rw [AffineTransfer.ofWord_append]
  exact hu.followedBy hv

/-- word realization の展開形。 -/
theorem realizes_iff (w : Word) (x y : ℕ) :
    Realizes w x y ↔
      2 ^ twoSteps w * y =
        3 ^ oddSteps w * x + affineConst w := by
  rfl

end Word
end Collatz2
