import CollatzLean.CollatzSecondLayer2.CertificateProjection
import CollatzLean.CollatzSecondLayer2.PreparedNormalizationTower

/-!
# capture normalizationの強い解析的四分岐

現在の正の三分岐で使われている「persistent captureと同じ項に
first-crossing由来の膨張prefixを添える」弱い接続とは区別し、
normalization trajectory自身から得られる四種類の正certificateをまとめる。

このファイルは四枝から最終三対象への射影を完全に証明する。
四枝のいずれかをpersistent capture familyから必ず構成する中心命題は、
`CaptureNormalizationAnalyticFourWayPrinciple`として一つの明示的な証明義務に隔離する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
direct affine transport係数がtower全体で一つの固定多項式以下である
Special C3 tower。
-/
structure PolynomialDirectSpecialTowerData (O : OddOrbit) where
  direct : DirectTransportSpecialTowerData O
  K : ℕ
  A : ℕ
  coefficientBound : ∀ j : ℕ,
    direct.coefficient j ≤
      K *
        (direct.tower.crossing.crossingLength
            (direct.tower.select j) + 1) ^ A

/--
同じmoving anchor上のnormalization trajectoryからlarge excursion certificateを
取り出したtower。
-/
structure TrajectoryLargeExcursionTowerData (O : OddOrbit) where
  tower : LargeExcursionTowerData O
  trajectory : ∀ j : ℕ,
    O.CaptureNormalizationTrajectory
      (tower.crossing.minima.index (tower.select j))
      (tower.crossing.crossingLength (tower.select j))

/--
normalization trajectory中のweak-expanding synchronized plateauから得たtower。
period長はcaptureに使ったq-window長と一致させる。
-/
structure TrajectoryWeakPlateauTowerData (O : OddOrbit) where
  tower : WeakPlateauTowerData O
  period_eq_window : ∀ j : ℕ,
    tower.periodLength j =
      tower.crossing.crossingLength (tower.select j)
  trajectory : ∀ j : ℕ,
    O.CaptureNormalizationTrajectory
      (tower.crossing.minima.index (tower.select j))
      (tower.crossing.crossingLength (tower.select j))

/-- persistent capture normalizationから生じる四種類の正の解析対象。 -/
inductive PersistentCaptureAnalyticOutcome
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) : Type
  | polynomialDirect
      (source : PreparedCaptureNormalizationTowerData P)
      (data : PolynomialDirectSpecialTowerData O)
  | largeExcursion
      (source : PreparedCaptureNormalizationTowerData P)
      (data : TrajectoryLargeExcursionTowerData O)
  | weakExpandingPlateau
      (source : PreparedCaptureNormalizationTowerData P)
      (data : TrajectoryWeakPlateauTowerData O)
  | eventuallySynchronized
      (source : PreparedCaptureNormalizationTowerData P)
      (data : EventuallySynchronizedMeanderData O)

/--
当初のcapture normalization解析で必要な中心原理。

ここではnormalization towerそのものは既に`P.normalizationTower hPersistent`で
構成済みであり、残る内容は、その実データから必ず

* 一様多項式direct transportを持つSpecial C3 tower
* trajectory由来large excursion tower
* trajectory由来weak-expanding plateau tower
* eventual synchronizationからactual化されたanchored meander

のいずれかを抽出する解析定理である。
-/
def CaptureNormalizationAnalyticFourWayPrinciple : Prop :=
  ∀ {O : OddOrbit} {F : MovingFirstCrossingData O},
    ∀ P : PolynomialPreparedFullWindowFamily F,
      ∀ _hPersistent : P.HasPersistentCapture,
        Nonempty (PersistentCaptureAnalyticOutcome P)

/-- polynomial direct枝はPolynomial Special C3 towerへ射影される。 -/
def PolynomialDirectSpecialTowerData.toPolynomialSpecialC3Tower
    {O : OddOrbit}
    (D : PolynomialDirectSpecialTowerData O) :
    PolynomialSpecialC3TowerData O :=
  D.direct.toPolynomialSpecialC3Tower

/-- trajectory large excursion枝はcritical expansion towerへ射影される。 -/
def TrajectoryLargeExcursionTowerData.toCriticalExpansionTower
    {O : OddOrbit}
    (D : TrajectoryLargeExcursionTowerData O) :
    CaptureGeneratedCriticalExpansionTowerData O :=
  D.tower.toCriticalExpansionTower

/-- trajectory weak plateau枝はcritical expansion towerへ射影される。 -/
def TrajectoryWeakPlateauTowerData.toCriticalExpansionTower
    {O : OddOrbit}
    (D : TrajectoryWeakPlateauTowerData O) :
    CaptureGeneratedCriticalExpansionTowerData O :=
  D.tower.toCriticalExpansionTower

/-- 四つの解析枝を最終三対象へ忘却する。 -/
theorem PersistentCaptureAnalyticOutcome.to_positive_trichotomy
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    {P : PolynomialPreparedFullWindowFamily F}
    (D : PersistentCaptureAnalyticOutcome P) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CaptureGeneratedCriticalExpansionTowerData O) := by
  cases D with
  | polynomialDirect _ S =>
      exact Or.inr (Or.inl ⟨S.toPolynomialSpecialC3Tower⟩)
  | largeExcursion _ E =>
      exact Or.inr (Or.inr ⟨E.toCriticalExpansionTower⟩)
  | weakExpandingPlateau _ W =>
      exact Or.inr (Or.inr ⟨W.toCriticalExpansionTower⟩)
  | eventuallySynchronized _ M =>
      exact Or.inl ⟨M.toAnchoredMeander⟩

/-- 四分岐原理からpersistent captureを最終三対象へ送る。 -/
theorem persistentCapture_strong_positive_reduction
    (hAnalytic : CaptureNormalizationAnalyticFourWayPrinciple)
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPersistent : P.HasPersistentCapture) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CaptureGeneratedCriticalExpansionTowerData O) := by
  rcases hAnalytic P hPersistent with ⟨D⟩
  exact D.to_positive_trichotomy

end CollatzSecondLayer2
