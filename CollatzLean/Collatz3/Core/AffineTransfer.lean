import CollatzLean.Collatz3.Arithmetic.Signed
import Mathlib.Tactic.Ring

/-!
# Collatz3: lossless affine transfer

有限区間の算術的正本は `D * y = P * x + A` を表す三成分だけとする。
符号分類、canonicality、軌道実現性はすべて後段の導出概念とする。
-/

namespace Collatz3

/-- `twoCoeff * y = oddCoeff * x + translate` を表す affine transfer。 -/
@[ext]
structure AffineTransfer where
  oddCoeff : ℕ
  twoCoeff : ℕ
  translate : ℕ
deriving DecidableEq

namespace AffineTransfer

/-- 空区間の恒等 transfer。 -/
def id : AffineTransfer :=
  { oddCoeff := 1, twoCoeff := 1, translate := 0 }

/-- `T` の後に `U` を実行する affine composition。 -/
def followedBy (T U : AffineTransfer) : AffineTransfer :=
  { oddCoeff := T.oddCoeff * U.oddCoeff
    twoCoeff := T.twoCoeff * U.twoCoeff
    translate := U.oddCoeff * T.translate +
      T.twoCoeff * U.translate }

@[simp] theorem id_oddCoeff : id.oddCoeff = 1 := rfl
@[simp] theorem id_twoCoeff : id.twoCoeff = 1 := rfl
@[simp] theorem id_translate : id.translate = 0 := rfl

@[simp] theorem followedBy_oddCoeff (T U : AffineTransfer) :
    (T.followedBy U).oddCoeff = T.oddCoeff * U.oddCoeff := rfl

@[simp] theorem followedBy_twoCoeff (T U : AffineTransfer) :
    (T.followedBy U).twoCoeff = T.twoCoeff * U.twoCoeff := rfl

@[simp] theorem followedBy_translate (T U : AffineTransfer) :
    (T.followedBy U).translate =
      U.oddCoeff * T.translate + T.twoCoeff * U.translate := rfl

@[simp] theorem id_followedBy (T : AffineTransfer) :
    id.followedBy T = T := by
  cases T
  simp [followedBy, id]

@[simp] theorem followedBy_id (T : AffineTransfer) :
    T.followedBy id = T := by
  cases T
  simp [followedBy, id]

/-- composition は結合的。 -/
theorem followedBy_assoc (T U V : AffineTransfer) :
    (T.followedBy U).followedBy V = T.followedBy (U.followedBy V) := by
  apply AffineTransfer.ext <;> simp [followedBy] <;> ring

/-- 2 側係数と 3 側係数の情報を失わない符号付き差。 -/
def signedScaleGap (T : AffineTransfer) : ℤ :=
  Arithmetic.delta T.twoCoeff T.oddCoeff

end AffineTransfer
end Collatz3
