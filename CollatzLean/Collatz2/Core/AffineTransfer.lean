import CollatzLean.Collatz2.Core.Word

/-!
# Collatz2: affine transfer

有限語の正本を `Expanding` / `Contracting` などの符号射影ではなく、

  `A * y = C * x + B`

を保持する affine transfer として扱う。

二つの語の連結は transfer の composition そのものであり、
後続する局所概念はこの lossless な三成分から導出する。
-/

namespace Collatz2

/--
有限区間の affine transfer。
`twoCoeff * y = oddCoeff * x + translate` を表す。
-/
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

/--
`T.followedBy U` は first `T`, followedBy `U` の composition。

`T : x -> y`, `U : y -> z` なら `T.followedBy U : x -> z`。
-/
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

/-- transfer composition は結合的。 -/
theorem followedBy_assoc (T U V : AffineTransfer) :
    (T.followedBy U).followedBy V = T.followedBy (U.followedBy V) := by
  apply AffineTransfer.ext <;> simp [followedBy] <;> ring

/-- 有限 exponent word の affine transfer。 -/
def ofWord (w : Word) : AffineTransfer :=
  { oddCoeff := 3 ^ Word.oddSteps w
    twoCoeff := 2 ^ Word.twoSteps w
    translate := Word.affineConst w }

@[simp] theorem ofWord_oddCoeff (w : Word) :
    (ofWord w).oddCoeff = 3 ^ Word.oddSteps w := rfl

@[simp] theorem ofWord_twoCoeff (w : Word) :
    (ofWord w).twoCoeff = 2 ^ Word.twoSteps w := rfl

@[simp] theorem ofWord_translate (w : Word) :
    (ofWord w).translate = Word.affineConst w := rfl

@[simp] theorem ofWord_nil :
    ofWord ([] : Word) = id := by
  rfl

/-- word append は transfer composition と exact に一致する。 -/
theorem ofWord_append (u v : Word) :
    ofWord (u ++ v) = (ofWord u).followedBy (ofWord v) := by
  apply AffineTransfer.ext
  · simp [ofWord, followedBy, pow_add]
  · simp [ofWord, followedBy, pow_add]
  · simp [ofWord, followedBy, Word.affineConst_append]

/-- transfer の signed diagonal determinant `C - A`。 -/
def determinant (T : AffineTransfer) : ℤ :=
  (T.oddCoeff : ℤ) - (T.twoCoeff : ℤ)

@[simp] theorem determinant_id : determinant id = 0 := by
  simp [determinant, id]

/-- word transfer の determinant。 -/
theorem determinant_ofWord (w : Word) :
    determinant (ofWord w) =
      (3 : ℤ) ^ Word.oddSteps w -
        (2 : ℤ) ^ Word.twoSteps w := by
  simp [determinant, ofWord]

/-- composition の determinant law。 -/
theorem determinant_followedBy (T U : AffineTransfer) :
    determinant (T.followedBy U) =
      (U.oddCoeff : ℤ) * determinant T +
        (T.twoCoeff : ℤ) * determinant U := by
  simp [determinant, followedBy]
  ring

end AffineTransfer
end Collatz2
