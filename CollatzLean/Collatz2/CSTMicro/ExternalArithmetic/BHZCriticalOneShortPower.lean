import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyOneShortSquares
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33ActualStage

/-!
# BHZ exact initial power から one-short square へ

BHZ Proposition 3.3 が与える exact initial period length が
`2*root-1` 以上なら、完全 square の一文字手前でも Pure B に必要な
one-short square が得られる。

ここでは standard / semistandard の二 family に対する eligibility を
exact numerator のまま定義する。uniform band や Rhin は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- standard candidate が one-short square に十分な長さを持つ。 -/
def BHZStandardOneShortEligible
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : Prop :=
  2 * bhzCriticalStandardRoot k - 1 ≤
    bhzCriticalStandardPowerNumerator P k

/-- semistandard candidate が source 条件と one-short 長さを満たす。 -/
def BHZSemistandardOneShortEligible
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : Prop :=
  0 < P.digit k ∧
  P.digit k < criticalBHZa k ∧
  2 * bhzCriticalSemistandardRoot P k - 1 ≤
    bhzCriticalSemistandardPowerNumerator P k

/-- 完全 square eligibility は standard one-short eligibility を含意する。 -/
theorem BHZStandardSquareEligible.toOneShort
    {s k : ℕ}
    {P : CriticalBHZPhasePacket s}
    (H : BHZStandardSquareEligible P k) :
    BHZStandardOneShortEligible P k := by
  exact le_trans
    (Nat.sub_le (2 * bhzCriticalStandardRoot k) 1)
    H

/-- 完全 square eligibility は semistandard one-short eligibility を含意する。 -/
theorem BHZSemistandardSquareEligible.toOneShort
    {s k : ℕ}
    {P : CriticalBHZPhasePacket s}
    (H : BHZSemistandardSquareEligible P k) :
    BHZSemistandardOneShortEligible P k := by
  refine ⟨H.1, H.2.1, ?_⟩
  exact le_trans
    (Nat.sub_le (2 * bhzCriticalSemistandardRoot P k) 1)
    H.2.2

/-- actual BHZ standard initial power から one-short square を得る。 -/
theorem actualBHZCritical_standard_oneShortSquareAt
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hRootTwo : 2 ≤ bhzCriticalStandardRoot k)
    (hOneShort : BHZStandardOneShortEligible P k) :
    CriticalBeattyOneShortSquareAt
      s (bhzCriticalStandardRoot k) := by
  have hPeriod :=
    actualBHZCritical_standard_initial_period P k hk
  exact
    hPeriod.toCriticalBeattyOneShortSquareAt
      hRootTwo hOneShort

/-- actual BHZ semistandard initial power から one-short square を得る。 -/
theorem actualBHZCritical_semistandard_oneShortSquareAt
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hRootTwo : 2 ≤ bhzCriticalSemistandardRoot P k)
    (hOneShort : BHZSemistandardOneShortEligible P k) :
    CriticalBeattyOneShortSquareAt
      s (bhzCriticalSemistandardRoot P k) := by
  have hPeriod :=
    actualBHZCritical_semistandard_initial_period
      P k hk hOneShort.1 hOneShort.2.1
  exact
    hPeriod.toCriticalBeattyOneShortSquareAt
      hRootTwo hOneShort.2.2

end ExternalArithmetic
end CSTMicro
end Collatz2
