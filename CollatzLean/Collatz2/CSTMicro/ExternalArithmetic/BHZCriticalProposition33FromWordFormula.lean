import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalStandardSemistandardWords
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33Port

/-!
# Inhabit `BHZCriticalProposition33` from the literal BHZ word formula

前段の `BHZCriticalProposition33` は

  exact root length + initial periodicity

だけを要求する project-facing port だった。

本ファイルでは abstraction boundary を BHZ Proposition 3.3 の source statement まで
下げる。すなわち source theorem が残す obligation は次のものだけ：

* standard canonical morphism word の cyclic permutation が actual shifted word の
  exact-length prefix powerを与える。
* `0<c_k<a_k` の semistandard canonical morphism word について同じことが成り立つ。

canonical word 自体、cyclic root の長さ、q_k / q_k-c_k q_(k-1) への変換、
cyclic prefix power から initial period への変換はすべて Lean 内で行う。

したがって old `C_BHZ` / uniform band / Rhin / Pure B data はこの boundary から消える。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace BHZCriticalCyclicPrefixPower

/--
A cyclic prefix power gives an actual initial period with period equal to the
canonical root length.
-/
theorem toCriticalShiftInitialPeriod
    {s length : ℕ}
    {canonical : List Bool}
    (H : BHZCriticalCyclicPrefixPower s canonical length)
    (hCanonicalPos : 0 < canonical.length) :
    CriticalShiftInitialPeriod
      s canonical.length length := by
  have hRootLen :
      H.root.length = canonical.length :=
    H.root_length_eq
  refine ⟨hCanonicalPos, ?_⟩
  intro i hi
  have hi0 : i < length := by
    omega
  rw [H.initialAgreement i hi0]
  rw [H.initialAgreement (i + canonical.length) hi]
  have hPeriod :=
    bhzPeriodicBit_add_length H.root i
  rw [hRootLen] at hPeriod
  exact hPeriod.symm

end BHZCriticalCyclicPrefixPower

/--
BHZ Proposition 3.3 in its literal source-shaped finite-word form.

This is deliberately narrower than `BHZCriticalProposition33`:
root arithmetic and periodicity are no longer assumed independently.
The source supplies only the claimed cyclic standard/semistandard prefix powers.
-/
structure BHZCriticalProposition33WordFormula where
  standard_prefix_power :
    ∀ {s : ℕ}
      (P : CriticalBHZPhasePacket s)
      (k : ℕ),
      1 ≤ k →
      BHZCriticalCyclicPrefixPower
        s
        (bhzCriticalStandardWord k)
        (bhzCriticalStandardPowerNumerator P k)

  semistandard_prefix_power :
    ∀ {s : ℕ}
      (P : CriticalBHZPhasePacket s)
      (k : ℕ),
      1 ≤ k →
      0 < P.digit k →
      P.digit k < criticalBHZa k →
      BHZCriticalCyclicPrefixPower
        s
        (bhzCriticalSemistandardWord P k)
        (bhzCriticalSemistandardPowerNumerator P k)

namespace BHZCriticalProposition33WordFormula

/--
The literal BHZ word formula inhabits the existing exact Proposition 3.3 port.
-/
theorem toProposition33
    (W : BHZCriticalProposition33WordFormula) :
    BHZCriticalProposition33 := {
  standard_initial_period := by
    intro s P k hk
    have hPower := W.standard_prefix_power P k hk
    have hLen := bhzCriticalStandardWord_length k
    have hPos : 0 < (bhzCriticalStandardWord k).length := by
      rw [hLen]
      exact criticalBHZq_pos k
    have hPeriod :=
      hPower.toCriticalShiftInitialPeriod hPos
    simpa [bhzCriticalStandardRoot, hLen] using hPeriod

  semistandard_initial_period := by
    intro s P k hk hDigitPos hDigitLt
    have hk2 : 2 ≤ k := by
      by_contra hNot
      have hkEq : k = 1 := by omega
      subst k
      simp at hDigitPos
    have hDigitLe : P.digit k ≤ criticalBHZa k := by
      omega
    have hPower :=
      W.semistandard_prefix_power
        P k hk hDigitPos hDigitLt
    have hLen :=
      bhzCriticalSemistandardWord_length
        P hk2 hDigitLe
    have hRootPos :=
      bhzCriticalSemistandardRoot_pos
        P hk2 hDigitLt
    have hPos :
        0 < (bhzCriticalSemistandardWord P k).length := by
      rw [hLen]
      exact hRootPos
    have hPeriod :=
      hPower.toCriticalShiftInitialPeriod hPos
    simpa [hLen] using hPeriod
}

/-- Named standard initial-period theorem from the literal word formula. -/
theorem standard_initial_period
    (W : BHZCriticalProposition33WordFormula)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k) :
    CriticalShiftInitialPeriod
      s
      (bhzCriticalStandardRoot k)
      (bhzCriticalStandardPowerNumerator P k) :=
  W.toProposition33.standard_initial_period P k hk

/-- Named semistandard initial-period theorem from the literal word formula. -/
theorem semistandard_initial_period
    (W : BHZCriticalProposition33WordFormula)
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
  W.toProposition33.semistandard_initial_period
    P k hk hDigitPos hDigitLt

/--
Once the exact standard source power is square-eligible, it is an actual
`CriticalBeattySquareAt` without any band constant.
-/
theorem standard_squareAt
    (W : BHZCriticalProposition33WordFormula)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZStandardSquareEligible P k) :
    CriticalBeattySquareAt
      s
      (bhzCriticalStandardRoot k) :=
  W.toProposition33.standard_squareAt P hk hSquare

/-- Semistandard source power -> actual Beatty square. -/
theorem semistandard_squareAt
    (W : BHZCriticalProposition33WordFormula)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZSemistandardSquareEligible P k) :
    CriticalBeattySquareAt
      s
      (bhzCriticalSemistandardRoot P k) :=
  W.toProposition33.semistandard_squareAt P hk hSquare

end BHZCriticalProposition33WordFormula

end ExternalArithmetic
end CSTMicro
end Collatz2
