import CollatzLean.CollatzSecondLayer2.DirectAffineTransport
import CollatzLean.CollatzSecondLayer2.ExcursionCertificate
import CollatzLean.CollatzSecondLayer2.WeakPlateauCertificate


/-!
# capture normalization trajectoryのcertificate分類

無限trajectoryは最初のdeferredまたはeventual synchronizationへ分かれる。
有限deferred側には、その有限解析区間に対するdirect affine transportを
明示的に付加する。large excursionとweak plateauは、より強い正のcertificateを
得た場合に同じ分類型へ載せるための独立constructorとして保持する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 最初のdeferredまでの有限語にdirect transport評価を付加したcertificate。 -/
structure DirectNormalizationCertificate
    {O : OddOrbit} {start q : ℕ}
    (T : O.CaptureNormalizationTrajectory start q) where
  deferred : OddOrbit.FirstDeferredNormalizationData T
  coefficient : ℕ
  transport :
    DirectAffineTransportBound coefficient
      (O.segmentWord start (deferred.terminalTime + q))

/-- normalization trajectoryの四種類の正certificate。 -/
inductive CaptureNormalizationClassification
    {O : OddOrbit} {start q : ℕ}
    (T : O.CaptureNormalizationTrajectory start q) : Type
  | direct (data : DirectNormalizationCertificate T)
  | largeExcursion {totalLength : ℕ}
      (data : LargeExcursionCertificate O start totalLength)
  | weakPlateau {totalLength : ℕ}
      (data : WeakExpandingPlateauCertificate O start totalLength q)
  | eventuallySynchronized
      (data : OddOrbit.EventuallySynchronizedNormalizationData T)

/--
任意のnormalization trajectoryは、少なくともdirect finite certificateまたは
 eventual synchronization certificateを持つ。large excursion / weak plateauの
強いcertificateが別途得られた場合も同じ分類型へ載せられる。
-/
theorem captureNormalizationClassification_nonempty
    {O : OddOrbit} {start q : ℕ}
    (T : O.CaptureNormalizationTrajectory start q) :
    Nonempty (CaptureNormalizationClassification T) := by
  rcases OddOrbit.captureNormalizationOutcome_nonempty T with ⟨h⟩
  cases h with
  | firstDeferred D =>
      let w := O.segmentWord start (D.terminalTime + q)
      let C := 3 ^ oddSteps w + affineConst w
      exact ⟨CaptureNormalizationClassification.direct
        { deferred := D
          coefficient := C
          transport := by
            simpa [w, C] using directAffineTransportBound w }⟩
  | eventuallySynchronized S =>
      exact ⟨CaptureNormalizationClassification.eventuallySynchronized S⟩

/-- large excursion certificateをtrajectory分類へ載せる。 -/
def CaptureNormalizationClassification.ofLargeExcursion
    {O : OddOrbit} {start q totalLength : ℕ}
    {T : O.CaptureNormalizationTrajectory start q}
    (C : LargeExcursionCertificate O start totalLength) :
    CaptureNormalizationClassification T :=
  CaptureNormalizationClassification.largeExcursion C

/-- weak plateau certificateをtrajectory分類へ載せる。 -/
def CaptureNormalizationClassification.ofWeakPlateau
    {O : OddOrbit} {start q totalLength : ℕ}
    {T : O.CaptureNormalizationTrajectory start q}
    (C : WeakExpandingPlateauCertificate O start totalLength q) :
    CaptureNormalizationClassification T :=
  CaptureNormalizationClassification.weakPlateau C

end CollatzSecondLayer2
