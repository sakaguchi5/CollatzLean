import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds
import CollatzLean.CollatzSecondLayer3.FirstDeferredSubsequenceClassification

/-!
# no-critical枝からdiscounted Special C3へ

no-critical first-deferred項ではterminal endpointが

`2^q * endpoint ≤ polynomial(q) * 3^q`

を満たす。このscaled上界とterminal deferred三分岐を組み合わせ、十分長い項では
large endpoint枝を排除してactual Special C3を得る。

Polynomial Special C3とdiscounted Special C3を、共通の中央枝
`SpecialC3ObstructionTowerData`へまとめる。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

structure DiscountedSpecialC3TowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  special : ∀ j : ℕ,
    SpecialC3At O
      (crossing.minima.index (select j) + offset j)
      (crossing.crossingLength (select j))
  K : ℕ
  A : ℕ
  scaledEndpointBound : ∀ j : ℕ,
    2 ^ crossing.crossingLength (select j) *
        O.value
          (crossing.minima.index (select j) + offset j +
            crossing.crossingLength (select j)) ≤
      (K * (crossing.crossingLength (select j) + 1) ^ A) *
        3 ^ crossing.crossingLength (select j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < crossing.crossingLength (select j)

inductive SpecialC3ObstructionTowerData (O : OddOrbit) : Type
  | polynomial (data : PolynomialSpecialC3TowerData O)
  | discounted (data : DiscountedSpecialC3TowerData O)

def HasSpecialC3ObstructionTowerOn (O : OddOrbit) : Prop :=
  Nonempty (SpecialC3ObstructionTowerData O)

def HasSpecialC3ObstructionTower : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧ HasSpecialC3ObstructionTowerOn O

namespace PolynomialSpecialC3TowerData

def toDiscounted
    {O : OddOrbit}
    (R : PolynomialSpecialC3TowerData O) :
    DiscountedSpecialC3TowerData O where
  crossing := R.crossing
  select := R.select
  select_strict := R.select_strict
  offset := R.offset
  special := R.special
  K := R.K
  A := R.A
  scaledEndpointBound := by
    intro j
    let q := R.crossing.crossingLength (R.select j)
    let y := O.value
      (R.crossing.minima.index (R.select j) + R.offset j + q)
    have hy : y ≤ R.K * (q + 1) ^ R.A := by
      simpa [q, y] using R.endpointBound j
    have h23 : 2 ^ q ≤ 3 ^ q := twoPow_le_threePow q
    calc
      2 ^ q * y ≤ 2 ^ q * (R.K * (q + 1) ^ R.A) :=
        Nat.mul_le_mul_left _ hy
      _ ≤ 3 ^ q * (R.K * (q + 1) ^ R.A) :=
        Nat.mul_le_mul_right _ h23
      _ = (R.K * (q + 1) ^ R.A) * 3 ^ q := by ring
  lengths_tend_to_infinity := R.lengths_tend_to_infinity

def toObstruction {O : OddOrbit} (R : PolynomialSpecialC3TowerData O) :
    SpecialC3ObstructionTowerData O := .polynomial R

end PolynomialSpecialC3TowerData

namespace DiscountedSpecialC3TowerData

def toObstruction {O : OddOrbit} (R : DiscountedSpecialC3TowerData O) :
    SpecialC3ObstructionTowerData O := .discounted R
end DiscountedSpecialC3TowerData

namespace SuperPolynomialNoCriticalFirstDeferredTowerData

noncomputable def discountedK
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (_R : SuperPolynomialNoCriticalFirstDeferredTowerData T) : ℕ :=
  (polynomialPreparedFullWindowFamily hGap D.crossing).K + 1

noncomputable def discountedA
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (_R : SuperPolynomialNoCriticalFirstDeferredTowerData T) : ℕ :=
  (polynomialPreparedFullWindowFamily hGap D.crossing).A + 1

noncomputable def discountedCutoff
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) : ℕ :=
  Classical.choose (polynomialBelowTwoPower R.discountedK R.discountedA)

theorem discountedCutoff_spec
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    ∀ q : ℕ, R.discountedCutoff ≤ q →
      R.discountedK * (q + 1) ^ R.discountedA < 2 ^ (q + 1) :=
  Classical.choose_spec (polynomialBelowTwoPower R.discountedK R.discountedA)

noncomputable def discountedTailStart
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) : ℕ :=
  Classical.choose
    (T.selected_lengths_tend_to_infinity R.select R.select_strict R.discountedCutoff)

theorem discountedTailStart_spec
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    ∀ j : ℕ, R.discountedTailStart ≤ j →
      R.discountedCutoff < T.windowLength (R.select j) :=
  Classical.choose_spec
    (T.selected_lengths_tend_to_infinity R.select R.select_strict R.discountedCutoff)

noncomputable def discountedSelect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) : ℕ :=
  R.select (R.discountedTailStart + j)

noncomputable def discountedCrossingSelect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) : ℕ := T.crossingIndex (R.discountedSelect j)

noncomputable def discountedOffset
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) : ℕ :=
  (polynomialPreparedFullWindowFamily hGap D.crossing).offset
      (R.discountedCrossingSelect j) +
    T.terminalTime (R.discountedSelect j)

theorem discountedCrossingSelect_strict
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    StrictMono R.discountedCrossingSelect := by
  intro a b hab
  change D.source.select
        (T.select (R.select (R.discountedTailStart + a))) <
      D.source.select
        (T.select (R.select (R.discountedTailStart + b)))
  exact D.source.select_strict
    (T.select_strict
      (R.select_strict (Nat.add_lt_add_left hab R.discountedTailStart)))

noncomputable def discountedSpecial
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) :
    SpecialC3At O
      (D.crossing.minima.index (R.discountedCrossingSelect j) +
        R.discountedOffset j)
      (D.crossing.crossingLength (R.discountedCrossingSelect j)) := by
  classical
  let n := R.discountedSelect j
  let q := T.windowLength n
  have hqCutoff : R.discountedCutoff ≤ q := by
    have h := R.discountedTailStart_spec (R.discountedTailStart + j) (by omega)
    simpa [n, q, discountedSelect] using h.le
  have hcoef := R.discountedCutoff_spec q hqCutoff
  have hscaled := T.terminalEndpoint_scaled_le_of_noCritical
    n (R.noCritical (R.discountedTailStart + j))
  have hNonempty : Nonempty
      (SpecialC3At O
        (D.crossing.minima.index (R.discountedCrossingSelect j) +
          R.discountedOffset j)
        (D.crossing.crossingLength (R.discountedCrossingSelect j))) := by
    rcases T.terminalEndpoint_large_or_special n with hlarge | hspecial
    · have hlower : 2 ^ (q + 1) * 3 ^ q <
          2 ^ q * T.terminalEndpoint n := by
        calc
          2 ^ (q + 1) * 3 ^ q = 2 ^ q * (2 * 3 ^ q) := by
            rw [pow_succ]; ring
          _ < 2 ^ q * T.terminalEndpoint n :=
            (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2 hlarge
      have hupper : 2 ^ q * T.terminalEndpoint n ≤
          (R.discountedK * (q + 1) ^ R.discountedA) * 3 ^ q := by
        simpa [n, q, discountedK, discountedA] using hscaled
      have hcoefScaled :
          (R.discountedK * (q + 1) ^ R.discountedA) * 3 ^ q <
            2 ^ (q + 1) * 3 ^ q :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).2 hcoef
      exfalso
      omega
    · simpa [discountedSelect, discountedCrossingSelect, discountedOffset,
        n, q, FirstDeferredNormalizationTowerData.start,
        FirstDeferredNormalizationTowerData.windowLength,
        FirstDeferredNormalizationTowerData.crossingIndex,
        StandardNormalizationGeneratedObstructionTowerData.start,
        StandardNormalizationGeneratedObstructionTowerData.windowLength,
        PolynomialPreparedFullWindowFamily.start, Nat.add_assoc] using hspecial
  exact Classical.choice hNonempty

noncomputable def toDiscountedSpecialC3Tower
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    DiscountedSpecialC3TowerData O where
  crossing := D.crossing
  select := R.discountedCrossingSelect
  select_strict := R.discountedCrossingSelect_strict
  offset := R.discountedOffset
  special := R.discountedSpecial
  K := R.discountedK
  A := R.discountedA
  scaledEndpointBound := by
    intro j
    let n := R.discountedSelect j
    have h := T.terminalEndpoint_scaled_le_of_noCritical
      n (R.noCritical (R.discountedTailStart + j))
    simpa [n, discountedSelect, discountedCrossingSelect, discountedOffset,
      discountedK, discountedA,
      FirstDeferredNormalizationTowerData.terminalEndpoint,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.terminalTime,
      FirstDeferredNormalizationTowerData.windowLength,
      FirstDeferredNormalizationTowerData.crossingIndex,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start, Nat.add_assoc] using h
  lengths_tend_to_infinity := by
    intro M
    obtain ⟨J, hJ⟩ := T.selected_lengths_tend_to_infinity
      R.select R.select_strict M
    refine ⟨J, ?_⟩
    intro j hj
    have h := hJ (R.discountedTailStart + j) (by omega)
    simpa [discountedCrossingSelect, discountedSelect,
      FirstDeferredNormalizationTowerData.windowLength,
      FirstDeferredNormalizationTowerData.crossingIndex,
      StandardNormalizationGeneratedObstructionTowerData.windowLength] using h

end SuperPolynomialNoCriticalFirstDeferredTowerData

end CollatzSecondLayer2
