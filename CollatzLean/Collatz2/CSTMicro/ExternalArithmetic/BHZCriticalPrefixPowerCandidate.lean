import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPhaseCoordinates

/-!
# Source-shaped BHZ initial-power candidate coordinates

This file does not yet prove Proposition 3.3.  It fixes the exact arithmetic
quantities that Proposition 3.3 uses, now in the repository's coordinates.

Index translation:

  BHZ q_k       = criticalBHZq k = criticalPowerP (k+1)
  BHZ c_k       = packet digit `c_k`
  BHZ a_k       = criticalBHZa k

Hence the two primitive-root lengths occurring in BHZ Proposition 3.3 become

  standard root      q_k,
  semistandard root  q_k - c_k q_(k-1).

The important design choice is that `c_k` is retained explicitly.  No
absolute `bandConstant` is introduced here.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- Standard BHZ primitive-root length `q_k`. -/
def bhzCriticalStandardRoot
    (k : ℕ) : ℕ :=
  criticalBHZq k

/-- Semistandard BHZ primitive-root length `q_k - c_k q_(k-1)`. -/
def bhzCriticalSemistandardRoot
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  criticalBHZq k - P.digit k * criticalBHZq (k - 1)

/--
BHZ residual prefix budget

  Σ_{j=1}^k (a_j-c_j) q_(j-1).

The `j=1` term is automatically zero for the critical slope because
`a_1=c_1=0`.
-/
def bhzCriticalResidualBudget
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 k)
    (fun j =>
      (criticalBHZa j - P.digit j) *
        criticalBHZq (j - 1))

/-- Indicator appearing in the standard-candidate formula of BHZ Prop. 3.3. -/
def bhzCriticalNextMaxIndicator
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  if criticalBHZa (k + 2) = P.digit (k + 2) then 1 else 0

/--
Numerator of the standard BHZ prefix exponent when written over denominator
`q_k`:

  1_{a_(k+2)=c_(k+2)} q_k
    + Σ_{j=1}^{k+1} (a_j-c_j) q_(j-1).
-/
def bhzCriticalStandardPowerNumerator
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  bhzCriticalNextMaxIndicator P k * criticalBHZq k +
    bhzCriticalResidualBudget P (k + 1)

/--
Numerator of the semistandard BHZ prefix exponent when written over root
`q_k-c_k q_(k-1)`:

  root + Σ_{j=1}^k (a_j-c_j) q_(j-1).
-/
def bhzCriticalSemistandardPowerNumerator
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  bhzCriticalSemistandardRoot P k +
    bhzCriticalResidualBudget P k

/-- Standard candidate has prefix exponent at least two. -/
def BHZStandardSquareEligible
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : Prop :=
  2 * bhzCriticalStandardRoot k ≤
    bhzCriticalStandardPowerNumerator P k

/-- Semistandard candidate has prefix exponent at least two. -/
def BHZSemistandardSquareEligible
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : Prop :=
  0 < P.digit k ∧
  P.digit k < criticalBHZa k ∧
  2 * bhzCriticalSemistandardRoot P k ≤
    bhzCriticalSemistandardPowerNumerator P k

/-- The two BHZ candidate families, before any square theorem is asserted. -/
inductive BHZCriticalPrefixPowerCandidateKind
  | standard
  | semistandard
  deriving DecidableEq, Repr

/--
Arithmetic candidate selected from a phase packet.

This structure deliberately contains no `CriticalBeattySquareAt` field yet.
That field will be supplied only after the S-adic semantic bridge and BHZ
Proposition 3.3 have been formalized.
-/
structure BHZCriticalPrefixPowerCandidate
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) where
  k : ℕ
  kind : BHZCriticalPrefixPowerCandidateKind
  root : ℕ
  root_eq :
    root =
      match kind with
      | .standard => bhzCriticalStandardRoot k
      | .semistandard => bhzCriticalSemistandardRoot P k

namespace BHZCriticalPrefixPowerCandidate

/-- Construct the standard arithmetic candidate at level `k`. -/
def standard
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    BHZCriticalPrefixPowerCandidate P := {
  k := k
  kind := .standard
  root := bhzCriticalStandardRoot k
  root_eq := rfl
}

/-- Construct the semistandard arithmetic candidate at level `k`. -/
def semistandard
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    BHZCriticalPrefixPowerCandidate P := {
  k := k
  kind := .semistandard
  root := bhzCriticalSemistandardRoot P k
  root_eq := rfl
}

end BHZCriticalPrefixPowerCandidate

end ExternalArithmetic
end CSTMicro
end Collatz2
