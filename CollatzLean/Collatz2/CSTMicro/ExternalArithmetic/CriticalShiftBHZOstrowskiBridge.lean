import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBHZIndexing

/-!
# Integer phase -> BHZ Ostrowski digits

This is the first replacement layer for the old uniform BHZ band assumption.

BHZ Proposition 2.7/2.8 uses digits `c_k` satisfying

  0 ≤ c_k ≤ a_k,
  c_(k+1) = a_(k+1) -> c_k = 0,

and the Ostrowski value uses the basis `q_(k-1)`.

The repository already has a bounded greedy expansion in the basis
`criticalPowerP k`.  `CriticalBHZIndexing` proves

  criticalPowerP k = BHZ q_(k-1),

so the two numeration systems differ only by indexing.

The type below rewrites the existing expansion in BHZ coordinates.  Its
`step` constructor is deliberately source-shaped:

* the new digit is `c_(K+1)`,
* it multiplies `q_K`,
* it is bounded by `a_(K+1)`,
* when it is maximal, the lower remainder is `< q_(K-1)`.

That last condition is the finite arithmetic form of the BHZ admissibility
rule forcing the preceding digit to vanish.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Finite BHZ-style Ostrowski expansion of an integer phase `s`.

The type index `K` is the highest BHZ digit index present.  Thus the stored
high-to-low digit list is

  [c_K, c_(K-1), ..., c_2],

while `c_1 = 0` is implicit because the critical slope has `a_1 = 0`.
-/
inductive BHZCriticalPhaseExpansion : (K s : ℕ) → Type
  | base
      (s : ℕ)
      (bound : s < criticalBHZq 2) :
      BHZCriticalPhaseExpansion 2 s
  | step
      {K s rem d : ℕ}
      (lower : BHZCriticalPhaseExpansion K rem)
      (bound : s < criticalBHZq (K + 1))
      (decomp : s = rem + d * criticalBHZq K)
      (digit_le : d ≤ criticalBHZa (K + 1))
      (max_remainder :
        d = criticalBHZa (K + 1) →
          rem < criticalBHZq (K - 1)) :
      BHZCriticalPhaseExpansion (K + 1) s

namespace BHZCriticalPhaseExpansion

/-- Highest BHZ index carried by an expansion is always at least two. -/
theorem top_ge_two
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    2 ≤ K := by
  induction E with
  | base => omega
  | step lower _ _ _ _ ih => omega

/-- Every encoded phase lies below the next BHZ denominator. -/
theorem bound
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    s < criticalBHZq K := by
  cases E with
  | base s h => exact h
  | step lower h _ _ _ => exact h

/-- BHZ digits in high-to-low order `[c_K,...,c_2]`. -/
def digitsHigh :
    {K s : ℕ} → BHZCriticalPhaseExpansion K s → List ℕ
  | _, _, .base s _ => [s]
  | _, _, .step (d := d) lower _ _ _ _ =>
      d :: digitsHigh lower

@[simp] theorem digitsHigh_length
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    E.digitsHigh.length = K - 1 := by
  induction E with
  | base s h => simp [digitsHigh]
  | @step K s rem d lower hb hdec hle hmax ih =>
      simp [digitsHigh, ih]
      have hK := lower.top_ge_two
      omega

/--
Evaluate a high-to-low BHZ digit list with weights
`q_(K-1), q_(K-2), ...`.
-/
def weightedValue : ℕ → List ℕ → ℕ
  | _, [] => 0
  | 0, _ :: _ => 0
  | K + 1, d :: ds =>
      d * criticalBHZq K + weightedValue K ds

/-- The digit list reconstructs the integer phase exactly. -/
theorem weightedValue_digitsHigh
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    weightedValue K E.digitsHigh = s := by
  induction E with
  | base s h =>
      simp [digitsHigh, weightedValue, criticalBHZq_one]
  | @step K s rem d lower hb hdec hle hmax ih =>
      have hK := lower.top_ge_two
      simp only [digitsHigh, weightedValue, ih]
      rw [hdec]
      omega

/-- Read a BHZ digit `c_k` from a high-to-low finite digit list. -/
def digitFromHigh : ℕ → List ℕ → ℕ → ℕ
  | _, [], _ => 0
  | 0, _ :: _, _ => 0
  | K + 1, d :: ds, k =>
      if k = K + 1 then d else digitFromHigh K ds k

/-- Digit accessor on a phase expansion. -/
def digit
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s)
    (k : ℕ) : ℕ :=
  digitFromHigh K E.digitsHigh k

/-- `c₁=0` for the critical slope convention. -/
@[simp] theorem digit_one
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    E.digit 1 = 0 := by
  unfold digit
  induction E with
  | base s h =>
      simp [digitsHigh, digitFromHigh]
  | @step K s rem d lower hb hdec hle hmax ih =>
      have hK := lower.top_ge_two
      simp [digitsHigh, digitFromHigh, ih]
      omega

end BHZCriticalPhaseExpansion

namespace ActualCriticalOstrowskiExpansion

/--
Exact re-indexing of the existing repository expansion into BHZ coordinates.

No new arithmetic hypothesis is introduced here.
-/
def toBHZCriticalPhase :
    {R n : ℕ} →
      ActualCriticalOstrowskiExpansion R n →
      BHZCriticalPhaseExpansion (R + 2) n
  | 0, _, .base n h =>
      .base n (by
        simpa [criticalBHZq] using h)
  | R + 1, _, .step (d := d) lower hBound hDec hDigit hMax =>
      .step
        (toBHZCriticalPhase lower)
        (by
          simpa [criticalBHZq, Nat.add_assoc] using hBound)
        (by
          simpa [criticalBHZq, Nat.add_assoc] using hDec)
        (by
          have hA :
              criticalBHZa (R + 3) =
                actualCriticalPartialQuotient (R + 3) :=
            criticalBHZa_eq_actual (by omega)
          simpa [hA, Nat.add_assoc] using hDigit)
        (by
          intro hd
          have hA :
              criticalBHZa (R + 3) =
                actualCriticalPartialQuotient (R + 3) :=
            criticalBHZa_eq_actual (by omega)
          have hd' :
              d = actualCriticalPartialQuotient (R + 3) := by
            simpa [hA] using hd
          have hr := hMax hd'
          simpa [criticalBHZq, Nat.add_assoc] using hr)

/-- Re-indexing preserves the actual digit list exactly. -/
theorem toBHZCriticalPhase_digitsHigh
    {R n : ℕ}
    (E : ActualCriticalOstrowskiExpansion R n) :
    E.toBHZCriticalPhase.digitsHigh = E.digits := by
  induction E with
  | base n h =>
      rfl
  | step lower hBound hDec hDigit hMax ih =>
      simp [
        toBHZCriticalPhase,
        BHZCriticalPhaseExpansion.digitsHigh,
        ActualCriticalOstrowskiExpansion.digits,
        ih
      ]

end ActualCriticalOstrowskiExpansion

/--
Canonical BHZ phase expansion attached to the integer shift `s`.

The deliberately generous top index `s+2` matches the repository's existing
canonical `actualCriticalOstrowskiDigits s`; leading digits may be zero.
-/
noncomputable def criticalShiftBHZExpansion
    (s : ℕ) : BHZCriticalPhaseExpansion (s + 2) s := by
  let E : ActualCriticalOstrowskiExpansion s s :=
    Classical.choice
      (exists_actualCriticalOstrowskiExpansion
        s s (self_lt_criticalPowerP_add_three s))
  simpa using E.toBHZCriticalPhase

/-- Canonical BHZ digits `[c_(s+2),...,c_2]` for phase `s`. -/
noncomputable def criticalShiftBHZDigitsHigh
    (s : ℕ) : List ℕ :=
  (criticalShiftBHZExpansion s).digitsHigh

/-- The canonical BHZ digit list reconstructs the shift amount exactly. -/
theorem criticalShiftBHZDigitsHigh_weightedValue
    (s : ℕ) :
    BHZCriticalPhaseExpansion.weightedValue
        (s + 2) (criticalShiftBHZDigitsHigh s) = s := by
  exact
    BHZCriticalPhaseExpansion.weightedValue_digitsHigh
      (criticalShiftBHZExpansion s)

/-- BHZ digit `c_k` attached canonically to the integer phase `s`. -/
noncomputable def criticalShiftBHZDigit
    (s k : ℕ) : ℕ :=
  (criticalShiftBHZExpansion s).digit k

@[simp] theorem criticalShiftBHZDigit_one
    (s : ℕ) :
    criticalShiftBHZDigit s 1 = 0 := by
  unfold criticalShiftBHZDigit
  exact BHZCriticalPhaseExpansion.digit_one _

end ExternalArithmetic
end CSTMicro
end Collatz2
