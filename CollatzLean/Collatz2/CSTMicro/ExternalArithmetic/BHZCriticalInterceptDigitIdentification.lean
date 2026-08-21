import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalIntegerOrbitConjugacy

/-!
# Identification of the actual BHZ intercept digits on the integer shift orbit

BHZ Proposition 2.7 attaches an admissible Ostrowski digit sequence `(c_k)` to
a Sturmian point.  Proposition 2.8 says that applying the Sturmian shift `T`
corresponds to applying the Ostrowski odometer `σ`.

For the characteristic point the coordinate is `0∞`.  Hence the point
`T^s w` has the finite Ostrowski coordinate of the integer `s`.

The repository has already constructed exactly that finite coordinate as
`criticalShiftBHZExpansion s`.  This file gives the source-facing names
"integer-orbit intercept digits" and identifies them with
`criticalShiftBHZDigit s k`.

No absolute square-band constant is introduced.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
BHZ intercept digit list for the natural-orbit point `T^s w`,
in the repository's finite high-to-low convention `[c_(s+2),...,c_2]`.
-/
noncomputable def bhzCriticalIntegerOrbitInterceptDigitsHigh
    (s : ℕ) : List ℕ :=
  (CriticalBHZPhasePacket.canonical s).digitsHigh

/-- BHZ intercept digit `c_k` for the natural-orbit point `T^s w`. -/
noncomputable def bhzCriticalIntegerOrbitInterceptDigit
    (s k : ℕ) : ℕ :=
  (CriticalBHZPhasePacket.canonical s).digit k

/--
The source-facing intercept digit list is exactly the canonical phase list
constructed from the integer Ostrowski expansion.
-/
theorem bhzCriticalIntegerOrbitInterceptDigitsHigh_eq
    (s : ℕ) :
    bhzCriticalIntegerOrbitInterceptDigitsHigh s =
      criticalShiftBHZDigitsHigh s := by
  rfl

/--
The source-facing intercept digit is exactly `criticalShiftBHZDigit`.
This is the identification used by the forthcoming BHZ Proposition 3.3 layer.
-/
theorem bhzCriticalIntegerOrbitInterceptDigit_eq
    (s k : ℕ) :
    bhzCriticalIntegerOrbitInterceptDigit s k =
      criticalShiftBHZDigit s k := by
  rfl

/-- For the critical slope one has `c₁=0`. -/
@[simp] theorem bhzCriticalIntegerOrbitInterceptDigit_one
    (s : ℕ) :
    bhzCriticalIntegerOrbitInterceptDigit s 1 = 0 := by
  rw [bhzCriticalIntegerOrbitInterceptDigit_eq]
  exact criticalShiftBHZDigit_one s

/--
The intercept digit list reconstructs the shift amount exactly:
`Σ c_k q_(k-1) = s`.
-/
theorem bhzCriticalIntegerOrbitInterceptDigits_weightedValue
    (s : ℕ) :
    BHZCriticalPhaseExpansion.weightedValue
        (s + 2)
        (bhzCriticalIntegerOrbitInterceptDigitsHigh s) = s := by
  exact
    (CriticalBHZPhasePacket.canonical s).weightedValue_eq_phase

/--
A finite source-shaped certificate that a digit list is an admissible BHZ
coordinate for the integer phase `s`.

Using the expansion object rather than only the weighted sum preserves the
digit bounds and maximal-digit carry rule already stored by
`BHZCriticalPhaseExpansion`.
-/
def IsBHZCriticalIntegerOrbitInterceptCoordinate
    (s : ℕ)
    (digitsHigh : List ℕ) : Prop :=
  ∃ E : BHZCriticalPhaseExpansion (s + 2) s,
    E.digitsHigh = digitsHigh

/-- The canonical intercept coordinate has the source-shaped certificate. -/
theorem bhzCriticalIntegerOrbitInterceptDigits_certified
    (s : ℕ) :
    IsBHZCriticalIntegerOrbitInterceptCoordinate
      s
      (bhzCriticalIntegerOrbitInterceptDigitsHigh s) := by
  refine
    ⟨(CriticalBHZPhasePacket.canonical s).expansion, ?_⟩
  rfl

/--
The certified digit coordinate evaluates to the actual shifted critical word.
-/
theorem bhzCriticalIntegerOrbitIntercept_evalBit
    (s n : ℕ) :
    bhzCriticalIntegerOrbitEvalBit
        (s + 2)
        (bhzCriticalIntegerOrbitInterceptDigitsHigh s)
        n =
      criticalShiftBit s n := by
  exact
    (CriticalBHZPhasePacket.canonical s).integerOrbitEvalBit_eq_shiftedBit n

end ExternalArithmetic
end CSTMicro
end Collatz2
