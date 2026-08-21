import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33FromWordFormula
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPrefixPowerSquare

/-!
# BHZ Proposition 3.3 morphism stage

この stage の chain は

  τ₀ / τ₁ finite morphisms
    -> critical directive image
    -> standard / semistandard canonical roots
    -> exact root lengths
         q_k
         q_k - c_k q_(k-1)
    -> cyclic prefix power (BHZ Proposition 3.3 source statement)
    -> CriticalShiftInitialPeriod
    -> BHZCriticalProposition33
    -> CriticalBeattySquareAt

である。

特に `BHZCriticalProposition33WordFormula.toProposition33` により、旧 abstract port
`BHZCriticalProposition33` は literal word formula から inhabit される。

残る BHZ-side source boundary は

  BHZCriticalProposition33WordFormula

の inhabitant、すなわち「actual shifted BHZ word が、論文に記された cyclic
standard / semistandard initial power を持つ」という Proposition 3.3 本文そのもの。

uniform `C_BHZ`、square band、Rhin exponent、Pure B state はこの boundary に含まれない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace BHZCriticalProposition33WordFormula

/-- Literal standard word formulaから realized square candidate まで一気に降ろす。 -/
def realizeStandardCandidate
    (W : BHZCriticalProposition33WordFormula)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k)
    (hSquare : BHZStandardSquareEligible P k) :
    BHZCriticalRealizedSquareCandidate P :=
  BHZCriticalPrefixPowerCandidate.realizeStandard
    W.toProposition33 P k hk hSquare

/-- Literal semistandard word formulaから realized square candidate まで降ろす。 -/
def realizeSemistandardCandidate
    (W : BHZCriticalProposition33WordFormula)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k)
    (hSquare : BHZSemistandardSquareEligible P k) :
    BHZCriticalRealizedSquareCandidate P :=
  BHZCriticalPrefixPowerCandidate.realizeSemistandard
    W.toProposition33 P k hk hSquare

end BHZCriticalProposition33WordFormula

/--
Standard root の Rhin handoff form。
The exact root is the existing actual power-Farey numerator `P_(k+1)`.
-/
theorem bhzCriticalStandardRoot_rhinHandoff
    (k : ℕ) :
    bhzCriticalStandardRoot k =
      criticalPowerP (k + 1) :=
  bhzCriticalStandardRoot_eq_criticalPowerP k

/--
Semistandard root の Rhin handoff form。
The phase dependence remains explicitly in the actual BHZ digit `c_k`.
-/
theorem bhzCriticalSemistandardRoot_rhinHandoff
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 1 ≤ k) :
    bhzCriticalSemistandardRoot P k =
      criticalPowerP (k + 1) -
        P.digit k * criticalPowerP k :=
  bhzCriticalSemistandardRoot_eq_criticalPowerP P hk

end ExternalArithmetic
end CSTMicro
end Collatz2
