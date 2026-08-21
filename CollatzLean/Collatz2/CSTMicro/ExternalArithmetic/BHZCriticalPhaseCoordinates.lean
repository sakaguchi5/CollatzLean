import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalShiftBHZOstrowskiBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyIncrementWord

/-!
# BHZ phase coordinates for the shifted critical Beatty word

BHZ の slope は `α = log₂ 3 - 1`。
従って word-side coordinate は

  beattyIndex (n+1) - beattyIndex n - 1

の binary word、すなわち `criticalBeattyIncrementBit` でなければならない。

注意:
Ferrers boundary 側の `criticalSturmianBit` は別 slope の mechanical word なので、
BHZ Proposition 3.3 の word coordinate としては使わない。

このファイルは

1. integer phase `s` の BHZ/Ostrowski digit coordinate、
2. 同じ phase から読む actual critical Beatty increment word、

を一つの packet に置く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- BHZ critical binary word を integer phase `s` から読む。 -/
def criticalShiftBit
    (s n : ℕ) : Bool :=
  criticalBeattyIncrementBit (s + n)

/-- Relative Beatty rise of the shifted critical word. -/
def criticalShiftRise
    (s k : ℕ) : ℕ :=
  beattyIndex (s + k) - beattyIndex s

@[simp] theorem criticalShiftRise_zero
    (s : ℕ) :
    criticalShiftRise s 0 = 0 := by
  simp [criticalShiftRise]

/-- Shift composition is exact on the BHZ word-side coordinate. -/
theorem criticalShiftBit_add_phase
    (s t n : ℕ) :
    criticalShiftBit (s + t) n =
      criticalShiftBit s (t + n) := by
  simp [criticalShiftBit, Nat.add_assoc]

/-- Shift composition is exact on relative Beatty rises. -/
theorem criticalShiftRise_add_phase
    (s t k : ℕ) :
    criticalShiftRise (s + t) k =
      beattyIndex (s + (t + k)) -
        beattyIndex (s + t) := by
  simp [criticalShiftRise, Nat.add_assoc]

/--
shifted BHZ bit の consecutive two-block equality から
`CriticalBeattySquareAt` を直接得る。
-/
theorem criticalBeattySquareAt_of_criticalShiftBit_blocks
    {s r : ℕ}
    (hr : 0 < r)
    (hBlock :
      ∀ i : ℕ, i < r →
        criticalShiftBit s i =
          criticalShiftBit s (r + i)) :
    CriticalBeattySquareAt s r := by
  apply
    criticalBeattySquareAt_of_incrementBit_blocks
      hr
  intro i hi
  have h := hBlock i hi
  simpa [criticalShiftBit, Nat.add_assoc] using h

/--
A packet carrying the two exact coordinates of the same integer phase.

* `digitsHigh` / `digit` are the BHZ/Ostrowski arithmetic coordinate;
* `shiftedBit` is the actual BHZ binary increment word;
* `shiftedRise` is the actual relative Beatty rise.
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

/-- Word-side shifted BHZ bit attached to the packet's phase. -/
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

/--
packet の shifted bit blocks が square なら actual Beatty square。
-/
theorem squareAt_of_shiftedBit_blocks
    {s r : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hr : 0 < r)
    (hBlock :
      ∀ i : ℕ, i < r →
        P.shiftedBit i =
          P.shiftedBit (r + i)) :
    CriticalBeattySquareAt s r := by
  exact
    criticalBeattySquareAt_of_criticalShiftBit_blocks
      hr hBlock

end CriticalBHZPhasePacket

/--
BHZ S-adic/Ostrowski evaluator と actual shifted BHZ word の semantic port。
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
