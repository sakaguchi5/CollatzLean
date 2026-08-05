import CollatzLean.CollatzSecondLayer2.NormalizationOutcomeSplit

/-!
# normalization refinementの正対象

標準構成由来normalization towerのfirst-deferred側で使う局所certificateと、
refinement後に残す二種類の正対象を定義する。

このファイルは対象の定義だけを担当する。first-deferred towerの分類と構成は
`FirstDeferredRefinement`で証明する。
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
  /-- capture直後は収縮側ではない。等号も含めて局所分類を初等的に保つ。 -/
  afterNoncontracting :
    2 ^ O.windowTwoSteps (start + time + 1) q ≤ 3 ^ q

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
  select : ℕ → ℕ
  select_strict : StrictMono select
  certificate : ∀ j : ℕ,
    CriticalCaptureInFirstDeferred (firstDeferred.data (select j))

namespace CriticalCaptureTowerData

/-- critical capture towerでもwindow長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : CriticalCaptureTowerData hGap O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.source.windowLength
        (D.firstDeferred.select (D.select j)) := by
  intro M
  obtain ⟨J, hJ⟩ :=
    D.firstDeferred.lengths_tend_to_infinity M
  have hselect_index : ∀ j : ℕ, j ≤ D.select j := by
    intro j
    induction j with
    | zero =>
        exact Nat.zero_le _
    | succ j ih =>
        have hstep :
            D.select j < D.select (j + 1) :=
          D.select_strict (Nat.lt_succ_self j)
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih hstep)
  refine ⟨J, ?_⟩
  intro j hj
  apply hJ (D.select j)
  exact le_trans hj (hselect_index j)

end CriticalCaptureTowerData

/-- plateau長が無限大へ進む、標準構成由来synchronized plateau tower。 -/
structure LongSynchronizedPlateauTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : StandardNormalizationGeneratedObstructionTowerData hGap O
  firstDeferred : FirstDeferredNormalizationTowerData source
  select : ℕ → ℕ
  select_strict : StrictMono select
  plateau : ∀ j : ℕ,
    SynchronizedPlateauInFirstDeferred (firstDeferred.data (select j))
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

end CollatzSecondLayer2
