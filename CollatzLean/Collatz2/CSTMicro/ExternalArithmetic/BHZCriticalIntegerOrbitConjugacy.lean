import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPhaseCoordinates

/-!
# BHZ critical integer-orbit odometer semantics

BHZ Proposition 2.8 identifies the Ostrowski odometer with the Sturmian shift.
For the present project we only need the natural orbit of the characteristic
critical word:

  0∞  --σ^s-->  c(s)
   |               |
   Ψ⁻¹             Ψ⁻¹
   |               |
  w   --T^s-->    T^s w.

The arithmetic side has already been constructed:
a `CriticalBHZPhasePacket s` carries admissible BHZ/Ostrowski digits whose
weighted value is exactly `s`.

This file gives the restricted conjugacy a concrete Lean semantics:
evaluate a finite BHZ digit list by its Ostrowski value, and then read the
actual critical word at that phase.  Thus the evaluator depends on the digit
coordinate, not on a hidden origin-prefix identification.

This is deliberately the integer-orbit part of BHZ Proposition 2.8.
It does not yet formalize the literal morphism composition
`T^c₁ τ₀^a₁ ∘ T^c₂ τ₁^a₂ ∘ ...`; that syntax is not needed to identify the
intercept digits of the actual shift orbit.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- A finite BHZ digit list evaluated as an integer Ostrowski phase. -/
def bhzCriticalDigitPhase
    (K : ℕ)
    (digitsHigh : List ℕ) : ℕ :=
  BHZCriticalPhaseExpansion.weightedValue K digitsHigh

/--
Read the critical Sturmian word from the phase encoded by a BHZ digit list.
-/
def bhzCriticalIntegerOrbitEvalBit
    (K : ℕ)
    (digitsHigh : List ℕ)
    (n : ℕ) : Bool :=
  criticalShiftBit
    (bhzCriticalDigitPhase K digitsHigh)
    n

/--
Relative Beatty rise read from the phase encoded by a BHZ digit list.
-/
def bhzCriticalIntegerOrbitEvalRise
    (K : ℕ)
    (digitsHigh : List ℕ)
    (k : ℕ) : ℕ :=
  criticalShiftRise
    (bhzCriticalDigitPhase K digitsHigh)
    k

namespace CriticalBHZPhasePacket

/-- The digit-side phase of a packet is exactly its integer phase. -/
theorem digitPhase_eq_phase
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    bhzCriticalDigitPhase (s + 2) P.digitsHigh = s := by
  simpa [bhzCriticalDigitPhase] using P.weightedValue_eq_phase

/--
The digit evaluator agrees exactly with the actual shifted critical bit.
-/
theorem integerOrbitEvalBit_eq_shiftedBit
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (n : ℕ) :
    bhzCriticalIntegerOrbitEvalBit
        (s + 2) P.digitsHigh n =
      P.shiftedBit n := by
  unfold bhzCriticalIntegerOrbitEvalBit
  rw [P.digitPhase_eq_phase]
  rfl

/--
The digit evaluator also agrees with the actual relative Beatty rise.
-/
theorem integerOrbitEvalRise_eq_shiftedRise
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalIntegerOrbitEvalRise
        (s + 2) P.digitsHigh k =
      P.shiftedRise k := by
  unfold bhzCriticalIntegerOrbitEvalRise
  rw [P.digitPhase_eq_phase]
  rfl

end CriticalBHZPhasePacket

/--
The restricted BHZ conjugacy on the natural orbit of the characteristic word.

The `digitsHigh` and `digit` fields are the Ostrowski coordinate,
while `evalBit` is the corresponding Sturmian point.
The last field is the commuting-square identity

  Ψ⁻¹(σ(c(s))) = T(Ψ⁻¹(c(s))).

On the natural orbit `σ(c(s))` is simply the coordinate of `s+1`.
-/
structure BHZCriticalIntegerOrbitConjugacy where
  digitsHigh : ℕ → List ℕ
  digit : ℕ → ℕ → ℕ
  evalBit : ℕ → ℕ → Bool

  phase_reconstruction :
    ∀ s : ℕ,
      BHZCriticalPhaseExpansion.weightedValue
          (s + 2) (digitsHigh s) = s

  digit_one_zero :
    ∀ s : ℕ,
      digit s 1 = 0

  shift_conjugacy :
    ∀ s n : ℕ,
      evalBit (s + 1) n =
        evalBit s (n + 1)

/--
The actual critical word and its canonical BHZ phase packets realize the
integer-orbit conjugacy.
-/
noncomputable def actualBHZCriticalIntegerOrbitConjugacy :
    BHZCriticalIntegerOrbitConjugacy := {
  digitsHigh :=
    fun s =>
      (CriticalBHZPhasePacket.canonical s).digitsHigh

  digit :=
    fun s k =>
      (CriticalBHZPhasePacket.canonical s).digit k

  evalBit :=
    fun s n =>
      criticalShiftBit s n

  phase_reconstruction := by
    intro s
    exact
      (CriticalBHZPhasePacket.canonical s).weightedValue_eq_phase

  digit_one_zero := by
    intro s
    change
      (CriticalBHZPhasePacket.canonical s).expansion.digit 1 = 0
    exact
      BHZCriticalPhaseExpansion.digit_one
        (CriticalBHZPhasePacket.canonical s).expansion

  shift_conjugacy := by
    intro s n
    simpa [Nat.add_comm] using
      criticalShiftBit_add_phase s 1 n
}

/-- Named commuting-square theorem for the actual integer orbit. -/
theorem actualBHZCriticalIntegerOrbit_shift_conjugacy
    (s n : ℕ) :
    actualBHZCriticalIntegerOrbitConjugacy.evalBit (s + 1) n =
      actualBHZCriticalIntegerOrbitConjugacy.evalBit s (n + 1) := by
  exact
    actualBHZCriticalIntegerOrbitConjugacy.shift_conjugacy s n

end ExternalArithmetic
end CSTMicro
end Collatz2
