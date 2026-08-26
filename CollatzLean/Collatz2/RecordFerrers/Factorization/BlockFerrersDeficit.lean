import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization

/-!
# Record–Ferrers Phase A: blockwise Ferrers deficit

critical roof budget と actual affine translation の差を、block composition と同じ重みで
transport する。global/local critical roof の差は signed carry correction として分離する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- word の critical roof budget から actual translation を引いた deficit。 -/
def wordCriticalDeficit (w : Word) : ℕ :=
  criticalAffineConst (oddSteps w) - affineConst w

/-- FirstCrossing では critical budget = deficit + actual translation。 -/
theorem criticalAffineConst_eq_wordCriticalDeficit_add_affineConst
    {w : Word}
    (hF : FirstCrossing w) :
    criticalAffineConst (oddSteps w) =
      wordCriticalDeficit w + affineConst w := by
  unfold wordCriticalDeficit
  have hLe := affineConst_le_criticalAffineConst_of_firstCrossing hF
  exact (Nat.sub_add_cancel hLe).symm

/-- local critical budgets の affine-composition weight 付き集約。 -/
def weightedLocalCriticalBudget : List Word → ℕ
  | [] => 0
  | b :: bs =>
      3 ^ oddSteps bs.flatten * criticalAffineConst (oddSteps b) +
        2 ^ twoSteps b * weightedLocalCriticalBudget bs

/-- local critical deficits の同じ affine weight 付き集約。 -/
def weightedLocalDeficit : List Word → ℕ
  | [] => 0
  | b :: bs =>
      3 ^ oddSteps bs.flatten * wordCriticalDeficit b +
        2 ^ twoSteps b * weightedLocalDeficit bs

/-- 全 block が FirstCrossing なら local critical budget は deficit + actual B に分解する。 -/
theorem weightedLocalCriticalBudget_eq_deficit_add_translation
    (bs : List Word)
    (hF : ∀ b ∈ bs, FirstCrossing b) :
    weightedLocalCriticalBudget bs =
      weightedLocalDeficit bs + weightedBlockTranslation bs := by
  revert hF
  induction bs with
  | nil =>
      intro _
      simp [weightedLocalCriticalBudget, weightedLocalDeficit,
        weightedBlockTranslation]
  | cons b bs ih =>
      intro hF
      have hbF : FirstCrossing b := hF b (by simp)
      have hTail : ∀ c ∈ bs, FirstCrossing c := by
        intro c hc
        exact hF c (by simp [hc])
      have hLocal :=
        criticalAffineConst_eq_wordCriticalDeficit_add_affineConst hbF
      have hIH := ih hTail
      simp only [weightedLocalCriticalBudget, weightedLocalDeficit,
        weightedBlockTranslation]
      rw [hLocal, hIH]
      ring

/-- global critical roof と blockwise local critical roofs の signed correction。 -/
def criticalCarryCorrectionZ (bs : List Word) : ℤ :=
  (criticalAffineConst (oddSteps bs.flatten) : ℤ) -
    (weightedLocalCriticalBudget bs : ℤ)

/--
global critical deficit = blockwise local deficits + critical carry correction。
-/
theorem wordCriticalDeficit_eq_carryCorrection_add_weightedLocal
    (bs : List Word)
    (hWhole : FirstCrossing bs.flatten)
    (hBlocks : ∀ b ∈ bs, FirstCrossing b) :
    (wordCriticalDeficit bs.flatten : ℤ) =
      criticalCarryCorrectionZ bs + (weightedLocalDeficit bs : ℤ) := by
  have hGlobal :=
    criticalAffineConst_eq_wordCriticalDeficit_add_affineConst hWhole
  have hLocal :=
    weightedLocalCriticalBudget_eq_deficit_add_translation bs hBlocks
  have hTranslation := weightedBlockTranslation_eq_affineConst_flatten bs
  have hGlobalZ :
      (criticalAffineConst (oddSteps bs.flatten) : ℤ) =
        (wordCriticalDeficit bs.flatten : ℤ) +
          (affineConst bs.flatten : ℤ) := by
    exact_mod_cast hGlobal
  have hLocalZ :
      (weightedLocalCriticalBudget bs : ℤ) =
        (weightedLocalDeficit bs : ℤ) +
          (weightedBlockTranslation bs : ℤ) := by
    exact_mod_cast hLocal
  have hTranslationZ :
      (weightedBlockTranslation bs : ℤ) = (affineConst bs.flatten : ℤ) := by
    exact_mod_cast hTranslation
  unfold criticalCarryCorrectionZ
  linarith

/-- Phase A Ferrers weighted area で見た critical complement。 -/
def shapeDeficit
    {p H : ℕ}
    (x : FiberPoint p H) : ℕ :=
  weightedArea (criticalShape p) - weightedArea x.toFerrersShape

/-- FirstCrossing fixed fiber では word critical deficit と weighted Ferrers complement が一致。 -/
theorem wordCriticalDeficit_eq_shapeDeficit
    {p H : ℕ}
    (x : FiberPoint p H)
    (hF : FirstCrossing x.word) :
    wordCriticalDeficit x.word = shapeDeficit x := by
  have hpPos : 0 < p := by
    have hLenPos : 0 < x.word.length :=
      List.length_pos_iff.mpr hF.nonempty
    have hLen : x.word.length = p := by
      simpa [oddSteps] using x.oddSteps_eq
    omega
  have hContract : ContractingChord p H := by
    have h := (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
    simpa [ContractingChord, x.oddSteps_eq, x.twoSteps_eq] using h
  have hShape : IsCriticalSubshape x.toFerrersShape :=
    (firstCrossing_iff_criticalSubshape x hpPos hContract).1 hF
  have hAreaLe := weightedArea_le_critical hShape
  have hActual := affineConst_eq_base_add_weightedArea x
  have hCritical := criticalAffineConst_eq_base_add_weightedArea p
  unfold wordCriticalDeficit shapeDeficit
  rw [x.oddSteps_eq, hActual, hCritical]
  omega

end RecordFerrers
end Collatz2
