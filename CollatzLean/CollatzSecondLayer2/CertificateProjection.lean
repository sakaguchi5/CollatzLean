import CollatzLean.CollatzSecondLayer2.PositiveObjects
import CollatzLean.CollatzSecondLayer2.DirectAffineTransport


/-!
# certificateから最終三対象への射影

各局所certificateを無理に同一視せず、tower化された正データから
最終三対象へ忘却する射影を固定する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- direct transport評価を備えたSpecial C3 tower。 -/
structure DirectTransportSpecialTowerData (O : OddOrbit) where
  tower : PolynomialSpecialC3TowerData O
  coefficient : ℕ → ℕ
  directTransport : ∀ j : ℕ,
    DirectAffineTransportBound (coefficient j)
      (O.segmentWord
        (tower.crossing.minima.index (tower.select j) + tower.offset j)
        (tower.crossing.crossingLength (tower.select j)))

/-- direct transport towerをPolynomial Special C3 towerへ射影する。 -/
def DirectTransportSpecialTowerData.toPolynomialSpecialC3Tower
    {O : OddOrbit}
    (D : DirectTransportSpecialTowerData O) :
    PolynomialSpecialC3TowerData O :=
  D.tower

/-- large excursion certificate列。 -/
structure LargeExcursionTowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  preparedOffset : ℕ → ℕ
  captured : ∀ j : ℕ,
    O.CapturedWindowAt
      (crossing.minima.index (select j) + preparedOffset j)
      (crossing.crossingLength (select j))
  certificate : ∀ j : ℕ,
    LargeExcursionCertificate O
      (crossing.minima.index (select j))
      (crossing.crossingLength (select j))
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (certificate j).blockLength

/-- large excursion towerはcapture-generated critical expansion tower。 -/
def LargeExcursionTowerData.toCriticalExpansionTower
    {O : OddOrbit}
    (D : LargeExcursionTowerData O) :
    CaptureGeneratedCriticalExpansionTowerData O where
  crossing := D.crossing
  select := D.select
  select_strict := D.select_strict
  preparedOffset := D.preparedOffset
  captured := D.captured
  excursion := D.certificate
  lengths_tend_to_infinity := D.lengths_tend_to_infinity

/-- weak plateau certificate列。 -/
structure WeakPlateauTowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  preparedOffset : ℕ → ℕ
  captured : ∀ j : ℕ,
    O.CapturedWindowAt
      (crossing.minima.index (select j) + preparedOffset j)
      (crossing.crossingLength (select j))
  periodLength : ℕ → ℕ
  certificate : ∀ j : ℕ,
    WeakExpandingPlateauCertificate O
      (crossing.minima.index (select j))
      (crossing.crossingLength (select j))
      (periodLength j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < ((certificate j).toLargeExcursion).blockLength

/-- weak plateau towerをcritical expansion towerへ射影する。 -/
def WeakPlateauTowerData.toCriticalExpansionTower
    {O : OddOrbit}
    (D : WeakPlateauTowerData O) :
    CaptureGeneratedCriticalExpansionTowerData O where
  crossing := D.crossing
  select := D.select
  select_strict := D.select_strict
  preparedOffset := D.preparedOffset
  captured := D.captured
  excursion := fun j => (D.certificate j).toLargeExcursion
  lengths_tend_to_infinity := D.lengths_tend_to_infinity

/-- eventual synchronization証明を付加したactual meander。 -/
structure EventuallySynchronizedMeanderData (O : OddOrbit) where
  meander : AnchoredOneSidedMeanderData O
  q : ℕ
  q_pos : 0 < q
  trajectory :
    O.CaptureNormalizationTrajectory meander.anchor q
  eventuallySynchronized :
    OddOrbit.EventuallySynchronizedNormalizationData trajectory

/-- eventual sync meanderを最終第一対象へ射影する。 -/
def EventuallySynchronizedMeanderData.toAnchoredMeander
    {O : OddOrbit}
    (D : EventuallySynchronizedMeanderData O) :
    AnchoredOneSidedMeanderData O :=
  D.meander

end CollatzSecondLayer2
