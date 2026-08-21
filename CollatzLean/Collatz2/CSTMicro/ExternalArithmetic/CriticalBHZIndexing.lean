import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

/-!
# Critical Sturmian continued-fraction coordinates in BHZ indexing

Berthé--Holton--Zamboni (BHZ) write the slope as

  α = [0; a₁ + 1, a₂, a₃, ...]

and use the convergent denominators `q_k`.  In the present repository the
power-Farey coordinates are shifted by one index:

  BHZ q_(k-1) = criticalPowerP k.

For the critical slope `α = log₂ 3 - 1` one has `a₁ = 0`.  For `k ≥ 2`,
BHZ `a_k` is exactly the already constructed
`actualCriticalPartialQuotient k`.

This file fixes that indexing once and for all.  Nothing about squares or
initial powers is assumed here.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- BHZ denominator `q_k` in the repository's actual critical coordinates. -/
def criticalBHZq (k : ℕ) : ℕ :=
  criticalPowerP (k + 1)

/--
BHZ numerator `p_k` for the slope `α = log₂ 3 - 1`.

The repository stores `(P,Q)` with `Q-P` equal to the numerator of the
corresponding convergent to `α`.
-/
def criticalBHZp (k : ℕ) : ℕ :=
  criticalPowerQ (k + 1) - criticalPowerP (k + 1)

/-- BHZ partial quotient `a_k` in the critical slope convention. -/
def criticalBHZa (k : ℕ) : ℕ :=
  if k = 1 then 0 else actualCriticalPartialQuotient k

@[simp] theorem criticalBHZa_one :
    criticalBHZa 1 = 0 := by
  simp [criticalBHZa]

/-- From index two onward, BHZ `a_k` is the actual recurrence coefficient. -/
theorem criticalBHZa_eq_actual
    {k : ℕ}
    (hk : 2 ≤ k) :
    criticalBHZa k = actualCriticalPartialQuotient k := by
  unfold criticalBHZa
  simp [show k ≠ 1 by omega]

@[simp] theorem criticalBHZq_zero :
    criticalBHZq 0 = 1 := by
  norm_num [
    criticalBHZq,
    criticalPowerP,
    criticalPowerConvergent,
    criticalInitialConvergent
  ]

@[simp] theorem criticalBHZq_one :
    criticalBHZq 1 = 1 := by
  norm_num [
    criticalBHZq,
    criticalPowerP,
    criticalPowerConvergent,
    criticalInitialConvergent
  ]

/-- The repository basis `P_k` is exactly BHZ `q_(k-1)`. -/
theorem criticalBHZq_pred_eq_criticalPowerP
    {k : ℕ}
    (hk : 1 ≤ k) :
    criticalBHZq (k - 1) = criticalPowerP k := by
  unfold criticalBHZq
  congr 1
  omega

/-- BHZ denominator recurrence in the repository's actual coordinates. -/
theorem criticalBHZq_recurrence
    {k : ℕ}
    (hk : 2 ≤ k) :
    criticalBHZq k =
      criticalBHZa k * criticalBHZq (k - 1) +
        criticalBHZq (k - 2) := by
  have hSpec := actualCriticalPartialQuotient_spec (r := k) hk
  unfold IsActualCriticalPartialQuotient at hSpec
  rw [criticalBHZa_eq_actual hk]
  unfold criticalBHZq
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 2 + 1 = k - 1 := by omega
  rw [hk1, hk2]
  rw [hSpec.2.1]
  omega

/-- `p_k + q_k` recovers the repository's `Q_(k+1)` coordinate. -/
theorem criticalBHZp_add_q
    (k : ℕ) :
    criticalBHZp k + criticalBHZq k = criticalPowerQ (k + 1) := by
  have hLe :
      criticalPowerP (k + 1) ≤ criticalPowerQ (k + 1) :=
    criticalPowerP_le_Q (k + 1)
  unfold criticalBHZp criticalBHZq
  omega

/-- The first nontrivial BHZ coefficient is `a₂ = 1`. -/
theorem criticalBHZa_two :
    criticalBHZa 2 = 1 := by
  rw [criticalBHZa_eq_actual (by omega : 2 ≤ 2)]
  have hSpec := actualCriticalPartialQuotient_spec (r := 2) (by omega)
  unfold IsActualCriticalPartialQuotient at hSpec
  norm_num [
    criticalPowerP,
    criticalPowerQ,
    criticalPowerConvergent,
    criticalInitialConvergent
  ] at hSpec
  omega

end ExternalArithmetic
end CSTMicro
end Collatz2
