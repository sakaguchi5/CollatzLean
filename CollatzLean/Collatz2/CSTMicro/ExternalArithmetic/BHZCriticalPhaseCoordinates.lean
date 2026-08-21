import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalShiftBHZOstrowskiBridge

/-!
# BHZ phase coordinates for the shifted critical word

There are two different objects which must not be silently identified:

1. the integer phase `s`, whose shifted critical word is obtained by reading
   the critical Beatty/Sturmian word from position `s`;
2. the BHZ Ostrowski digit vector `(c_k)` describing the same phase in the
   odometer/S-adic coordinate system.

`CriticalShiftBHZOstrowskiBridge` has already constructed the arithmetic
coordinate `(c_k)` and proved that its Ostrowski value is exactly `s`.

This file fixes the *word-side* coordinate of the same phase.  It does not yet
assert the BHZ multiplicative S-adic formula.  That is the next semantic
bridge to prove from BHZ Proposition 2.7/2.8.  Keeping the target explicit here
prevents the old mistake of treating an arbitrary shifted interval as an
origin prefix.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- The critical Sturmian bit seen from integer phase `s`. -/
def criticalShiftBit
    (s n : ℕ) : Bool :=
  criticalSturmianBit (s + n)

/-- Relative Beatty rise of the shifted critical word. -/
def criticalShiftRise
    (s k : ℕ) : ℕ :=
  beattyIndex (s + k) - beattyIndex s

@[simp] theorem criticalShiftRise_zero
    (s : ℕ) :
    criticalShiftRise s 0 = 0 := by
  simp [criticalShiftRise]

/-- Shift composition is exact on the word-side coordinate. -/
theorem criticalShiftBit_add_phase
    (s t n : ℕ) :
    criticalShiftBit (s + t) n =
      criticalShiftBit s (t + n) := by
  simp [criticalShiftBit, Nat.add_assoc]

/-- Shift composition is exact on relative Beatty rises. -/
theorem criticalShiftRise_add_phase
    (s t k : ℕ) :
    criticalShiftRise (s + t) k =
      beattyIndex (s + (t + k)) - beattyIndex (s + t) := by
  simp [criticalShiftRise, Nat.add_assoc]

/--
A packet carrying the two exact coordinates of the same integer phase.

* `digits` is the canonical BHZ/Ostrowski arithmetic coordinate;
* `bit` and `rise` are the actual shifted critical word coordinate.

The missing future theorem is not a field here: we do **not** assume that an
S-adic evaluator built from `digits` equals `bit`.  That equality must be
proved from the BHZ odometer conjugacy.
-/
structure CriticalBHZPhasePacket (s : ℕ) where
  expansion : BHZCriticalPhaseExpansion (s + 2) s

namespace CriticalBHZPhasePacket

/-- Canonical packet for every integer phase. -/
noncomputable def canonical
    (s : ℕ) : CriticalBHZPhasePacket s := {
  expansion := criticalShiftBHZExpansion s
}

/-- High-to-low BHZ digits of the packet. -/
def digitsHigh
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) : List ℕ :=
  P.expansion.digitsHigh

/-- BHZ digit `c_k` of the packet. -/
def digit
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  P.expansion.digit k

/-- The arithmetic phase encoded by the packet is exactly its type index `s`. -/
theorem weightedValue_eq_phase
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    BHZCriticalPhaseExpansion.weightedValue
        (s + 2) P.digitsHigh = s := by
  unfold digitsHigh
  exact P.expansion.weightedValue_digitsHigh

/-- Word-side shifted bit attached to the packet's phase. -/
def shiftedBit
    {s : ℕ}
    (_P : CriticalBHZPhasePacket s)
    (n : ℕ) : Bool :=
  criticalShiftBit s n

/-- Word-side relative Beatty rise attached to the packet's phase. -/
def shiftedRise
    {s : ℕ}
    (_P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  criticalShiftRise s k

end CriticalBHZPhasePacket

/--
The precise semantic obligation still required from BHZ Proposition 2.7/2.8.

`evalBit P n` is intended to be the bit obtained by evaluating the
multiplicative S-adic expansion with the packet's digits.  An inhabitant must
prove that this evaluator equals the actual shifted critical word.

This is intentionally an interface only; no inhabitant is asserted in this
file.
-/
structure BHZCriticalShiftSAdicSemantics where
  evalBit :
    ∀ {s : ℕ}, CriticalBHZPhasePacket s → ℕ → Bool
  shift_agreement :
    ∀ {s : ℕ}
      (P : CriticalBHZPhasePacket s)
      (n : ℕ),
      evalBit P n = P.shiftedBit n

end ExternalArithmetic
end CSTMicro
end Collatz2
