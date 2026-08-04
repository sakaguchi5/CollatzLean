import CollatzLean.CollatzSecondLayer2.NormalizationOutcomeSplit

/-!
# normalization obstructionのrefinement境界

raw normalization obstructionを無条件にfirst-deferred tower / eventual-sync towerへ
分けた後、最終的に残す二つの正対象を定義する。

* critical capture tower
* long synchronized plateau tower

このファイルでは、旧`CaptureNormalizationAnalyticFourWayPrinciple`のような
persistent captureからの一枚岩な外部原理には戻さない。残る証明義務を

* eventual-sync towerからanchored meanderをactual化する局所原理
* first-deferred towerをSpecial C3 / critical capture / long plateauへ分ける局所原理

の二つへ分離する。どちらも、既に無条件構成された標準towerを入力に取る。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 一つの有限normalization中でcritical shellを横断するactual capture。 -/
structure CriticalCaptureInFirstDeferred
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀) where
  time : ℕ
  time_lt_terminal : time < F.terminalTime
  captured : O.CapturedWindowAt (start + time) q
  beforeContracting :
    3 ^ q < 2 ^ O.windowTwoSteps (start + time) q
  afterExpanding :
    2 ^ O.windowTwoSteps (start + time + 1) q < 3 ^ q

/-- 一つの有限normalization中にある連続synchronized plateau。 -/
structure SynchronizedPlateauInFirstDeferred
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀) where
  offset : ℕ
  length : ℕ
  length_pos : 0 < length
  inside : offset + length ≤ F.terminalTime
  synchronized : ∀ t : ℕ, t < length →
    O.SynchronizedWindowAt (start + offset + t) q

/-- critical captureを無限に持つ、標準構成由来tower。 -/
structure CriticalCaptureTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : StandardNormalizationGeneratedObstructionTowerData hGap O
  firstDeferred : FirstDeferredNormalizationTowerData source
  certificate : ∀ j : ℕ,
    CriticalCaptureInFirstDeferred (firstDeferred.data j)

namespace CriticalCaptureTowerData

/-- critical capture towerでもwindow長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : CriticalCaptureTowerData hGap O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.source.windowLength (D.firstDeferred.select j) :=
  D.firstDeferred.lengths_tend_to_infinity

end CriticalCaptureTowerData

/-- plateau長が無限大へ進む、標準構成由来synchronized plateau tower。 -/
structure LongSynchronizedPlateauTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : StandardNormalizationGeneratedObstructionTowerData hGap O
  firstDeferred : FirstDeferredNormalizationTowerData source
  plateau : ∀ j : ℕ,
    SynchronizedPlateauInFirstDeferred (firstDeferred.data j)
  plateauLengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (plateau j).length

/-- refinement後に第三枝として残す二対象。 -/
inductive RefinedNormalizationObstructionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Type
  | criticalCapture
      (data : CriticalCaptureTowerData hGap O)
  | longSynchronizedPlateau
      (data : LongSynchronizedPlateauTowerData hGap O)

/-- 指定軌道上のrefined normalization obstruction。 -/
def HasRefinedNormalizationObstructionTowerOn
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Prop :=
  Nonempty (RefinedNormalizationObstructionTowerData hGap O)

/-- 非有界軌道上のrefined normalization obstruction。 -/
def HasRefinedNormalizationObstructionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧ HasRefinedNormalizationObstructionTowerOn hGap O

/-- eventual-sync towerからactual anchored meanderを抽出する局所証明義務。 -/
def EventuallySynchronizedTowerToMeanderPrinciple : Prop :=
  ∀ (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit),
    ∀ D : StandardNormalizationGeneratedObstructionTowerData hGap O,
      EventuallySynchronizedNormalizationTowerData D →
        Nonempty (AnchoredOneSidedMeanderData O)

/--
first-deferred towerを既存Special C3または残余二構造へ分ける局所証明義務。

入力は標準構成由来を保持したtowerであり、persistent captureや軌道全体から
新しい対象を仮定的に生成する原理ではない。
-/
def FirstDeferredTowerRefinementPrinciple : Prop :=
  ∀ (hGap : TwoThreeGapPolynomialBound)
    (_hPow : PolynomialBelowTwoPower)
    (O : OddOrbit),
    ∀ D : StandardNormalizationGeneratedObstructionTowerData hGap O,
      FirstDeferredNormalizationTowerData D →
        Nonempty (PolynomialSpecialC3TowerData O) ∨
          Nonempty (CriticalCaptureTowerData hGap O) ∨
          Nonempty (LongSynchronizedPlateauTowerData hGap O)

/--
二つの局所refinement原理から、標準normalization towerを既存二枝と残余二構造へ送る。
-/
theorem standardNormalization_refinement
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_outcomeTower_dichotomy D with
    hFirst | hEventually
  · rcases hFirst with ⟨F⟩
    rcases hDeferred hGap hPow O D F with
      hSpecial | hCritical | hPlateau
    · exact Or.inr (Or.inl hSpecial)
    · exact Or.inr (Or.inr
        ⟨RefinedNormalizationObstructionTowerData.criticalCapture
          (Classical.choice hCritical)⟩)
    · exact Or.inr (Or.inr
        ⟨RefinedNormalizationObstructionTowerData.longSynchronizedPlateau
          (Classical.choice hPlateau)⟩)
  · rcases hEventually with ⟨E⟩
    exact Or.inl (hSync hGap O D E)

/-- 既存二対象を除外した文脈では、standard towerは残余二構造へ入る。 -/
theorem standardNormalization_residual_of_exclusions
    (hSync : EventuallySynchronizedTowerToMeanderPrinciple)
    (hDeferred : FirstDeferredTowerRefinementPrinciple)
    (hGap : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    {O : OddOrbit}
    (hMeander : ¬ Nonempty (AnchoredOneSidedMeanderData O))
    (hSpecial : ¬ Nonempty (PolynomialSpecialC3TowerData O))
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (RefinedNormalizationObstructionTowerData hGap O) := by
  rcases standardNormalization_refinement
      hSync hDeferred hGap hPow D with hM | hS | hR
  · exact False.elim (hMeander hM)
  · exact False.elim (hSpecial hS)
  · exact hR

end CollatzSecondLayer2
