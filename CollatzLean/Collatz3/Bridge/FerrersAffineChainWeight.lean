import Mathlib.Data.Real.Basic
import CollatzLean.Collatz3.Bridge.FerrersAffineCellWeight
import Mathlib.Tactic.FieldSimp

/-!
# Collatz3 Bridge: Ferrers cell chain の weighted telescope

`FerrersCellStep` を有限回つないだ chain を、開始 word・終了 word・総 affine weight の
三つだけで薄く保持する。

各 step が

`affineConst(before) = affineConst(after) + cellWeight`

を満たすため、chain 全体では exact に

`affineConst(start) = affineConst(finish) + totalWeight`

となる。

Young/Ferrers 図で複数セルを追加したとき、単なる cell 数ではなく各セルの
Collatz affine numerator 寄与を加算した量が exact に telescope することを表す。
-/

namespace Collatz3
namespace Word

/--
weighted 1-cell step の有限 chain。
第三引数は chain 内の cell weight の総和。
-/
inductive FerrersCellChain : Word → Word → ℕ → Prop
  | refl (w : Word) : FerrersCellChain w w 0
  | step
      {w₀ w₁ w₂ : Word}
      {cell total : ℕ}
      (hStep : FerrersCellStep w₀ w₁ cell)
      (hTail : FerrersCellChain w₁ w₂ total) :
      FerrersCellChain w₀ w₂ (cell + total)

namespace FerrersCellChain

/-- Ferrers chain は odd-step 数を保存する。 -/
theorem oddSteps_eq
    {w₀ w₁ : Word}
    {total : ℕ}
    (h : FerrersCellChain w₀ w₁ total) :
    oddSteps w₀ = oddSteps w₁ := by
  induction h with
  | refl w => rfl
  | step hStep hTail ih =>
      exact (hStep.length_depth_eq.1).trans ih

/-- Ferrers chain は total two-depth を保存する。 -/
theorem twoSteps_eq
    {w₀ w₁ : Word}
    {total : ℕ}
    (h : FerrersCellChain w₀ w₁ total) :
    twoSteps w₀ = twoSteps w₁ := by
  induction h with
  | refl w => rfl
  | step hStep hTail ih =>
      exact (hStep.length_depth_eq.2).trans ih

/--
Ferrers chain の weighted-cell telescope。

`affineConst(start) = affineConst(finish) + totalWeight`。
-/
theorem affineConst_eq
    {w₀ w₁ : Word}
    {total : ℕ}
    (h : FerrersCellChain w₀ w₁ total) :
    affineConst w₀ = affineConst w₁ + total := by
  induction h with
  | refl w => simp
  | step hStep hTail ih =>
      have hLocal := hStep.affineConst_eq
      omega


/--
weighted telescope を full `3^p` scale で正規化した形。

`B(start)/3^p = B(finish)/3^p + totalWeight/3^p`。
-/
theorem normalized_affineConst_eq
    {w₀ w₁ : Word}
    {total : ℕ}
    (h : FerrersCellChain w₀ w₁ total) :
    (affineConst w₀ : ℝ) / (3 : ℝ) ^ oddSteps w₀ =
      (affineConst w₁ : ℝ) / (3 : ℝ) ^ oddSteps w₀ +
        (total : ℝ) / (3 : ℝ) ^ oddSteps w₀ := by
  have hNat := h.affineConst_eq
  have hReal :
      (affineConst w₀ : ℝ) = (affineConst w₁ : ℝ) + (total : ℝ) := by
    exact_mod_cast hNat
  field_simp
  exact hReal

/-- chain の total weight は endpoints の affineConst 差として一意。 -/
theorem total_unique
    {w₀ w₁ : Word}
    {s t : ℕ}
    (hs : FerrersCellChain w₀ w₁ s)
    (ht : FerrersCellChain w₀ w₁ t) :
    s = t := by
  have hsEq := hs.affineConst_eq
  have htEq := ht.affineConst_eq
  omega

end FerrersCellChain
end Word
end Collatz3
