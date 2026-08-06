import CollatzLean.CollatzFirstLayer.AffineTransport
import CollatzLean.CollatzSecondLayer3.CaptureRefinement



/-!
# affine transportからpolynomial prepared refinementへ

capture正規化区間の輸送係数と開始値がwindow長に対して多項式小なら、
`endpoint_le_polynomial_of_transport`からendpoint多項式上界を自動生成する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- transport評価を備えたmoving prepared refinement列。 -/
structure TransportPreparedRefinementSequence
    {O : OddOrbit} (F : MovingFirstCrossingData O) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  length : ℕ → ℕ
  insideCrossing : ∀ j : ℕ,
    offset j + length j ≤ F.crossingLength (select j)
  start_strict : StrictMono
    (fun j => F.minima.index (select j) + offset j)
  packet : ∀ j : ℕ,
    O.PreparedWindowPacket
      (F.minima.index (select j) + offset j)
      (length j)
  coefficient : ℕ → ℕ
  transport : ∀ j : ℕ,
    TransportBound (coefficient j)
      (O.segmentWord
        (F.minima.index (select j) + offset j)
        (length j))
  Kc : ℕ
  B : ℕ
  coefficientBound : ∀ j : ℕ,
    coefficient j ≤ Kc * (length j + 1) ^ B
  Kx : ℕ
  A : ℕ
  startBound : ∀ j : ℕ,
    O.value (F.minima.index (select j) + offset j) ≤
      Kx * (length j + 1) ^ A
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace TransportPreparedRefinementSequence

/-- transport評価からendpoint多項式上界付きrefinementを構成する。 -/
def toPolynomialPreparedRefinementSequence
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : TransportPreparedRefinementSequence F) :
    PolynomialPreparedRefinementSequence F where
  select := R.select
  select_strict := R.select_strict
  offset := R.offset
  length := R.length
  insideCrossing := R.insideCrossing
  start_strict := R.start_strict
  packet := R.packet
  K := R.Kc * (R.Kx + 1)
  A := R.B + R.A + 1
  endpointBound := by
    intro j
    let s := F.minima.index (R.select j) + R.offset j
    let q := R.length j
    have hrun :
        Realizes (O.segmentWord s q) (O.value s) (O.value (s + q)) :=
      O.realizes_segment s q
    have hlen :
        (O.segmentWord s q).length ≤ 1 * (q + 1) ^ 1 := by
      simp
    have hy := endpoint_le_polynomial_of_transport
      (q := q)
      hrun (R.transport j)
      (R.coefficientBound j)
      (R.startBound j)
      hlen
    simpa [s, q, Nat.add_assoc] using hy
  lengths_tend_to_infinity := R.lengths_tend_to_infinity

/--
transport-polynomial refinementはpersistent captureまたはSpecial C3 refinement。
-/
theorem persistentCapture_or_specialC3
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : TransportPreparedRefinementSequence F) :
    R.toPolynomialPreparedRefinementSequence.HasPersistentCapture ∨
      HasSpecialC3From F :=
  R.toPolynomialPreparedRefinementSequence.persistentCapture_or_specialC3

end TransportPreparedRefinementSequence
end CollatzSecondLayer2
