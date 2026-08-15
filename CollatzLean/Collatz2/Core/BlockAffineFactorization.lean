import CollatzLean.Collatz2.Core.BoundaryForm
import CollatzLean.Collatz2.Core.TranslationPath

/-!
# Collatz2 Core: block affine factorization

word を任意の block 列へ分割したとき、global transfer / translation を
block transfer / translation から lossless に再構成する一般 API。
record / mountain のどちらにも依存しない。
-/

namespace Collatz2
namespace Word

/-- block 列を順に composition した transfer。 -/
def composedBlockTransfer : List Word → AffineTransfer
  | [] => AffineTransfer.id
  | b :: bs => (AffineTransfer.ofWord b).followedBy (composedBlockTransfer bs)

/-- block 列の translation を固定係数付きで再帰的に集約する。 -/
def weightedBlockTranslation : List Word → ℕ
  | [] => 0
  | b :: bs =>
      3 ^ oddSteps bs.flatten * affineConst b +
        2 ^ twoSteps b * weightedBlockTranslation bs

/-- block 列の global odd-step 数。 -/
def blockOddSteps (bs : List Word) : ℕ :=
  (bs.map oddSteps).sum

/-- block 列の global two-depth。 -/
def blockTwoSteps (bs : List Word) : ℕ :=
  (bs.map twoSteps).sum

@[simp] theorem oddSteps_flatten_blocks (bs : List Word) :
    oddSteps bs.flatten = blockOddSteps bs := by
  induction bs with
  | nil => simp [blockOddSteps, oddSteps]
  | cons b bs ih =>
      simp [blockOddSteps, ih]

@[simp] theorem twoSteps_flatten_blocks (bs : List Word) :
    twoSteps bs.flatten = blockTwoSteps bs := by
  induction bs with
  | nil => simp [blockTwoSteps, twoSteps]
  | cons b bs ih =>
      simp [blockTwoSteps, ih]

/-- flatten した word transfer は block composition と exact に一致。 -/
theorem composedBlockTransfer_eq_ofWord_flatten
    (bs : List Word) :
    composedBlockTransfer bs = AffineTransfer.ofWord bs.flatten := by
  induction bs with
  | nil =>
      simp [composedBlockTransfer]
  | cons b bs ih =>
      change
        (AffineTransfer.ofWord b).followedBy (composedBlockTransfer bs) =
          AffineTransfer.ofWord (b ++ bs.flatten)
      rw [ih, AffineTransfer.ofWord_append]

/-- global `B` は block `B_i` の固定係数付き再帰和。 -/
theorem weightedBlockTranslation_eq_affineConst_flatten
    (bs : List Word) :
    weightedBlockTranslation bs = affineConst bs.flatten := by
  induction bs with
  | nil =>
      simp [weightedBlockTranslation]
  | cons b bs ih =>
      change
        3 ^ oddSteps bs.flatten * affineConst b +
            2 ^ twoSteps b * weightedBlockTranslation bs =
          affineConst (b ++ bs.flatten)
      rw [affineConst_append, ih]

/-- block transfer の translation component も同じ weighted sum。 -/
theorem composedBlockTransfer_translate
    (bs : List Word) :
    (composedBlockTransfer bs).translate = weightedBlockTranslation bs := by
  rw [composedBlockTransfer_eq_ofWord_flatten]
  simp [weightedBlockTranslation_eq_affineConst_flatten]

/--
任意の block factorization で global boundary form は composed transfer の boundary form。
-/
theorem boundaryForm_blocks
    (bs : List Word)
    (x y : ℕ) :
    AffineTransfer.boundaryForm (composedBlockTransfer bs) x y =
      AffineTransfer.boundaryForm (AffineTransfer.ofWord bs.flatten) x y := by
  rw [composedBlockTransfer_eq_ofWord_flatten]

end Word
end Collatz2
