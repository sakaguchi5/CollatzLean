import CollatzLean.Collatz2.Geometry.IntegerFerrersDeficit
import CollatzLean.Collatz2.Geometry.MinimalCrossingBlock
import CollatzLean.Collatz2.Core.BlockAffineFactorization

/-!
# Collatz2 Geometry: blockwise Ferrers deficit

local critical budgets / local Ferrers deficits を block composition と同じ重みで transport し、
global deficit と local deficits の差を critical carry correction として exact に分離する。
-/

namespace Collatz2
namespace Word

/-- local critical budgets の affine-composition weight 付き集約。 -/
def weightedLocalCriticalBudget : List Word → ℕ
  | [] => 0
  | b :: bs =>
      3 ^ oddSteps bs.flatten * criticalAffineConst (oddSteps b) +
        2 ^ twoSteps b * weightedLocalCriticalBudget bs

/-- local integer Ferrers deficits の同じ affine weight 付き集約。 -/
def weightedLocalFerrersDeficit : List Word → ℕ
  | [] => 0
  | b :: bs =>
      3 ^ oddSteps bs.flatten * integerFerrersDeficit b +
        2 ^ twoSteps b * weightedLocalFerrersDeficit bs

/-- 全 block が FirstCrossing なら local critical budget は deficit + actual B に分解する。 -/
theorem weightedLocalCriticalBudget_eq_deficit_add_translation
    (bs : List Word)
    (hF : ∀ b ∈ bs, FirstCrossing b) :
    weightedLocalCriticalBudget bs =
      weightedLocalFerrersDeficit bs + weightedBlockTranslation bs := by
  induction bs with
  | nil =>
      simp [weightedLocalCriticalBudget, weightedLocalFerrersDeficit,
        weightedBlockTranslation]
  | cons b bs ih =>
      have hbF : FirstCrossing b := hF b (by simp)
      have htail : ∀ c ∈ bs, FirstCrossing c := by
        intro c hc
        exact hF c (by simp [hc])
      have hLocal :=
        criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hbF
      have hIH := ih htail
      simp only [weightedLocalCriticalBudget, weightedLocalFerrersDeficit,
        weightedBlockTranslation]
      rw [hLocal, hIH]
      ring

/--
global critical roof と blockwise local critical roofs の signed correction。
carry の正値性を仮定せず exact identity を先に保持する。
-/
def criticalCarryCorrectionZ (bs : List Word) : ℤ :=
  (criticalAffineConst (oddSteps bs.flatten) : ℤ) -
    (weightedLocalCriticalBudget bs : ℤ)

/--
global Ferrers deficit = blockwise local deficits + critical carry correction。
-/
theorem integerFerrersDeficit_eq_carryCorrection_add_weightedLocal
    (bs : List Word)
    (hWhole : FirstCrossing bs.flatten)
    (hBlocks : ∀ b ∈ bs, FirstCrossing b) :
    (integerFerrersDeficit bs.flatten : ℤ) =
      criticalCarryCorrectionZ bs +
        (weightedLocalFerrersDeficit bs : ℤ) := by
  have hGlobal :=
    criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hWhole
  have hLocal :=
    weightedLocalCriticalBudget_eq_deficit_add_translation bs hBlocks
  have hTranslation := weightedBlockTranslation_eq_affineConst_flatten bs
  have hGlobalZ :
      (criticalAffineConst (oddSteps bs.flatten) : ℤ) =
        (integerFerrersDeficit bs.flatten : ℤ) +
          (affineConst bs.flatten : ℤ) := by
    exact_mod_cast hGlobal
  have hLocalZ :
      (weightedLocalCriticalBudget bs : ℤ) =
        (weightedLocalFerrersDeficit bs : ℤ) +
          (weightedBlockTranslation bs : ℤ) := by
    exact_mod_cast hLocal
  have hTranslationZ :
      (weightedBlockTranslation bs : ℤ) = (affineConst bs.flatten : ℤ) := by
    exact_mod_cast hTranslation
  unfold criticalCarryCorrectionZ
  linarith

/-- minimal record decorations は blockwise theorem の仮定を自動的に満たす。 -/
theorem integerFerrersDeficit_eq_carryCorrection_add_weightedLocal_of_minimal
    (bs : List Word)
    (hWhole : FirstCrossing bs.flatten)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b) :
    (integerFerrersDeficit bs.flatten : ℤ) =
      criticalCarryCorrectionZ bs +
        (weightedLocalFerrersDeficit bs : ℤ) := by
  apply integerFerrersDeficit_eq_carryCorrection_add_weightedLocal bs hWhole
  intro b hb
  exact (hMinimal b hb).firstCrossing


/-! ## record anchor を含む factorization -/

/--
record blocks の前にある anchor は local FirstCrossing block とは限らないので、
anchor 自身は actual `B` のまま、record blocks だけを local critical budget へ持ち上げる。
-/
def weightedRecordLocalCriticalBudget
    (anchor : Word)
    (bs : List Word) : ℕ :=
  3 ^ oddSteps bs.flatten * affineConst anchor +
    2 ^ twoSteps anchor * weightedLocalCriticalBudget bs

/-- record blocks の local Ferrers deficits を anchor transfer で transport した量。 -/
def weightedRecordLocalFerrersDeficit
    (anchor : Word)
    (bs : List Word) : ℕ :=
  2 ^ twoSteps anchor * weightedLocalFerrersDeficit bs

/--
各 record block が FirstCrossing なら、anchor を含む local critical budget は
transported local deficit + genuine global `B` に exact 分解する。
-/
theorem weightedRecordLocalCriticalBudget_eq_deficit_add_translation
    (anchor : Word)
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, FirstCrossing b) :
    weightedRecordLocalCriticalBudget anchor bs =
      weightedRecordLocalFerrersDeficit anchor bs +
        affineConst (anchor ++ bs.flatten) := by
  have hLocal :=
    weightedLocalCriticalBudget_eq_deficit_add_translation bs hBlocks
  have hTranslation := weightedBlockTranslation_eq_affineConst_flatten bs
  unfold weightedRecordLocalCriticalBudget weightedRecordLocalFerrersDeficit
  rw [hLocal, hTranslation, affineConst_append]
  ring

/--
global critical roof と anchor+local-record critical budgets の signed carry correction。
record carry の 0/1 geometry をさらに展開する前の exact residual として保持する。
-/
def recordCriticalCarryCorrectionZ
    (anchor : Word)
    (bs : List Word) : ℤ :=
  (criticalAffineConst (oddSteps (anchor ++ bs.flatten)) : ℤ) -
    (weightedRecordLocalCriticalBudget anchor bs : ℤ)

/--
anchor を含む genuine global FirstCrossing word では

global Ferrers deficit
  = record carry correction + transported local Ferrers deficits

が exact に成り立つ。
-/
theorem integerFerrersDeficit_anchor_eq_carryCorrection_add_weightedLocal
    (anchor : Word)
    (bs : List Word)
    (hWhole : FirstCrossing (anchor ++ bs.flatten))
    (hBlocks : ∀ b ∈ bs, FirstCrossing b) :
    (integerFerrersDeficit (anchor ++ bs.flatten) : ℤ) =
      recordCriticalCarryCorrectionZ anchor bs +
        (weightedRecordLocalFerrersDeficit anchor bs : ℤ) := by
  have hGlobal :=
    criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hWhole
  have hLocal :=
    weightedRecordLocalCriticalBudget_eq_deficit_add_translation
      anchor bs hBlocks
  have hGlobalZ :
      (criticalAffineConst (oddSteps (anchor ++ bs.flatten)) : ℤ) =
        (integerFerrersDeficit (anchor ++ bs.flatten) : ℤ) +
          (affineConst (anchor ++ bs.flatten) : ℤ) := by
    exact_mod_cast hGlobal
  have hLocalZ :
      (weightedRecordLocalCriticalBudget anchor bs : ℤ) =
        (weightedRecordLocalFerrersDeficit anchor bs : ℤ) +
          (affineConst (anchor ++ bs.flatten) : ℤ) := by
    exact_mod_cast hLocal
  unfold recordCriticalCarryCorrectionZ
  linarith

/-- minimal record decorations では local FirstCrossing 仮定は自動。 -/
theorem integerFerrersDeficit_anchor_eq_carryCorrection_add_weightedLocal_of_minimal
    (anchor : Word)
    (bs : List Word)
    (hWhole : FirstCrossing (anchor ++ bs.flatten))
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b) :
    (integerFerrersDeficit (anchor ++ bs.flatten) : ℤ) =
      recordCriticalCarryCorrectionZ anchor bs +
        (weightedRecordLocalFerrersDeficit anchor bs : ℤ) := by
  apply integerFerrersDeficit_anchor_eq_carryCorrection_add_weightedLocal
    anchor bs hWhole
  intro b hb
  exact (hMinimal b hb).firstCrossing

end Word
end Collatz2
