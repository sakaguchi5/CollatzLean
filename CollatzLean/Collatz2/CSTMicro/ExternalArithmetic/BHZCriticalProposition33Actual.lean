import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZPublishedProposition33Canonical

/-!
# Actual inhabitant of BHZ Proposition 3.3 for the critical shifted word

Published BHZ Proposition 3.3 is stated for the unique Ostrowski coordinate of
the actual Sturmian point.  The project-facing `BHZCriticalProposition33WordFormula`
quantifies over any `CriticalBHZPhasePacket s`.

`BHZCriticalPhaseDigitUniqueness` proved that every valid packet for the same
integer phase has exactly the same digits.  We may therefore transport the
canonical published theorem to an arbitrary packet without strengthening the
external theorem.

This file gives the closed inhabitants used downstream:

  actualBHZCriticalProposition33WordFormula
  actualBHZCriticalProposition33

No uniform square-band constant is introduced.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
Published canonical Prop.3.3 transported to the project-facing arbitrary
packet interface by exact Ostrowski digit uniqueness.
-/
noncomputable def actualBHZCriticalProposition33WordFormula :
    BHZCriticalProposition33WordFormula := {
  standard_prefix_power := by
    intro s P k hk
    let C : CriticalBHZPhasePacket s :=
      CriticalBHZPhasePacket.canonical s
    have hSource :
        BHZCriticalCyclicPrefixPower
          s
          (bhzCriticalStandardWord k)
          (bhzCriticalStandardPowerNumerator C k) := by
      dsimp [C]
      exact bhz2006_proposition33_standard_critical s k hk
    have hLength :
        bhzCriticalStandardPowerNumerator P k =
          bhzCriticalStandardPowerNumerator C k :=
      bhzCriticalStandardPowerNumerator_eq_of_same_phase P C k
    rw [hLength]
    exact hSource

  semistandard_prefix_power := by
    intro s P k hk hDigitPos hDigitLt
    let C : CriticalBHZPhasePacket s :=
      CriticalBHZPhasePacket.canonical s
    have hDigitEq : P.digit k = C.digit k :=
      P.digit_eq_of_same_phase C k
    have hDigitPosC : 0 < C.digit k := by
      rw [← hDigitEq]
      exact hDigitPos
    have hDigitLtC : C.digit k < criticalBHZa k := by
      rw [← hDigitEq]
      exact hDigitLt
    have hSource :
        BHZCriticalCyclicPrefixPower
          s
          (bhzCriticalSemistandardWord C k)
          (bhzCriticalSemistandardPowerNumerator C k) := by
      dsimp [C] at hDigitPosC hDigitLtC ⊢
      exact
        bhz2006_proposition33_semistandard_critical
          s k hk hDigitPosC hDigitLtC
    have hWord :
        bhzCriticalSemistandardWord P k =
          bhzCriticalSemistandardWord C k :=
      bhzCriticalSemistandardWord_eq_of_same_phase P C k
    have hLength :
        bhzCriticalSemistandardPowerNumerator P k =
          bhzCriticalSemistandardPowerNumerator C k :=
      bhzCriticalSemistandardPowerNumerator_eq_of_same_phase P C k
    rw [hWord, hLength]
    exact hSource
}

/-- Existing project-facing exact Proposition 3.3 port, now actually inhabited. -/
theorem actualBHZCriticalProposition33 :
    BHZCriticalProposition33 :=
  actualBHZCriticalProposition33WordFormula.toProposition33

/-- Actual standard initial-period theorem. -/
theorem actualBHZCritical_standard_initial_period
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k) :
    CriticalShiftInitialPeriod
      s
      (bhzCriticalStandardRoot k)
      (bhzCriticalStandardPowerNumerator P k) :=
  actualBHZCriticalProposition33.standard_initial_period P k hk

/-- Actual semistandard initial-period theorem. -/
theorem actualBHZCritical_semistandard_initial_period
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k)
    (hDigitPos : 0 < P.digit k)
    (hDigitLt : P.digit k < criticalBHZa k) :
    CriticalShiftInitialPeriod
      s
      (bhzCriticalSemistandardRoot P k)
      (bhzCriticalSemistandardPowerNumerator P k) :=
  actualBHZCriticalProposition33.semistandard_initial_period
    P k hk hDigitPos hDigitLt

/-- Square-eligible standard source candidate is an actual critical Beatty square. -/
theorem actualBHZCritical_standard_squareAt
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZStandardSquareEligible P k) :
    CriticalBeattySquareAt s (bhzCriticalStandardRoot k) :=
  actualBHZCriticalProposition33.standard_squareAt P hk hSquare

/-- Square-eligible semistandard source candidate is an actual critical Beatty square. -/
theorem actualBHZCritical_semistandard_squareAt
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZSemistandardSquareEligible P k) :
    CriticalBeattySquareAt s (bhzCriticalSemistandardRoot P k) :=
  actualBHZCriticalProposition33.semistandard_squareAt P hk hSquare

end ExternalArithmetic
end CSTMicro
end Collatz2
