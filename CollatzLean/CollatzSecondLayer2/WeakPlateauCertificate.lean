import CollatzLean.CollatzSecondLayer2.ExcursionCertificate


/-!
# weak-expanding plateau certificate

synchronized q-windowが長く続き、一周期が膨張側である有限構造を保存する。
回転後のactual expanding blockもcertificate自身に保持する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 長いsynchronized plateauと、その中の膨張rotation block。 -/
structure WeakExpandingPlateauCertificate
    (O : OddOrbit) (anchor totalLength q : ℕ) where
  q_pos : 0 < q
  plateauOffset : ℕ
  plateauLength : ℕ
  synchronized : ∀ t : ℕ, t < plateauLength →
    O.SynchronizedWindowAt (anchor + plateauOffset + t) q
  periodHeight : ℕ
  height_eq :
    O.windowTwoSteps (anchor + plateauOffset) q = periodHeight
  expandingPeriod : 2 ^ periodHeight < 3 ^ q
  rotationOffset : ℕ
  blockLength : ℕ
  blockLength_pos : 0 < blockLength
  block_inside :
    plateauOffset + rotationOffset + blockLength ≤ totalLength
  rotatedPrefixesExpanding : ∀ m : ℕ,
    0 < m → m ≤ blockLength →
    Expanding
      (O.segmentWord
        (anchor + plateauOffset + rotationOffset) m)

namespace WeakExpandingPlateauCertificate

/-- weak plateauが保存するrotation blockをlarge excursionとして忘却する。 -/
def toLargeExcursion
    {O : OddOrbit} {anchor totalLength q : ℕ}
    (P : WeakExpandingPlateauCertificate O anchor totalLength q) :
    LargeExcursionCertificate O anchor totalLength where
  blockOffset := P.plateauOffset + P.rotationOffset
  blockLength := P.blockLength
  length_pos := P.blockLength_pos
  inside := by simpa [Nat.add_assoc] using P.block_inside
  allPrefixesExpanding := by
    intro m hm hmlen
    simpa [Nat.add_assoc] using P.rotatedPrefixesExpanding m hm hmlen

end WeakExpandingPlateauCertificate
end CollatzSecondLayer2
