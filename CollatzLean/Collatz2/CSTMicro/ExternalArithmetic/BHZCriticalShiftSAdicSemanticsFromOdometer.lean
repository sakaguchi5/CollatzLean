import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalInterceptDigitIdentification

/-!
# Inhabit `BHZCriticalShiftSAdicSemantics` from the BHZ integer-orbit odometer

The existing semantic port asks for an evaluator built from a phase packet and
a proof that it equals the actual shifted critical word.

For the natural orbit of the characteristic critical word, BHZ Proposition
2.8 identifies the S-adic/Ostrowski coordinate with the shift coordinate.
The preceding files realize exactly this restricted conjugacy:

  digits --Ostrowski weighted value--> phase s --read--> T^s(w).

Thus the evaluator below depends on the packet's BHZ digit list and its
Ostrowski semantics.  It does not simply ignore the digit coordinate.

This is sufficient to use `criticalShiftBHZDigit s k` as the actual BHZ
intercept digit `c_k` in the next Proposition 3.3 formalization.

The literal finite-word morphisms `τ₀,τ₁` are intentionally left to the
Proposition 3.3 syntax layer; no uniform square-band hypothesis is used here.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Actual BHZ shift semantics on the natural integer orbit.
-/
noncomputable def actualBHZCriticalShiftSAdicSemantics :
    BHZCriticalShiftSAdicSemantics := {
  evalBit :=
    fun {s} P n =>
      bhzCriticalIntegerOrbitEvalBit
        (s + 2) P.digitsHigh n

  shift_agreement := by
    intro s P n
    exact P.integerOrbitEvalBit_eq_shiftedBit n
}

/-- Public evaluation theorem for the inhabited semantic port. -/
theorem actualBHZCriticalShiftSAdicSemantics_evalBit
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (n : ℕ) :
    actualBHZCriticalShiftSAdicSemantics.evalBit P n =
      P.shiftedBit n := by
  exact
    actualBHZCriticalShiftSAdicSemantics.shift_agreement P n

/--
Canonical specialization: the BHZ digit evaluator at phase `s` is exactly the
actual critical word shifted by `s`.
-/
theorem actualBHZCriticalShiftSAdicSemantics_canonical
    (s n : ℕ) :
    actualBHZCriticalShiftSAdicSemantics.evalBit
        (CriticalBHZPhasePacket.canonical s) n =
      criticalShiftBit s n := by
  exact
    actualBHZCriticalShiftSAdicSemantics_evalBit
      (CriticalBHZPhasePacket.canonical s) n

/--
The digit named `criticalShiftBHZDigit s k` may now be read as the BHZ
integer-orbit intercept digit `c_k`.
-/
theorem criticalShiftBHZDigit_eq_actualBHZInterceptDigit
    (s k : ℕ) :
    criticalShiftBHZDigit s k =
      bhzCriticalIntegerOrbitInterceptDigit s k := by
  exact
    (bhzCriticalIntegerOrbitInterceptDigit_eq s k).symm

end ExternalArithmetic
end CSTMicro
end Collatz2
