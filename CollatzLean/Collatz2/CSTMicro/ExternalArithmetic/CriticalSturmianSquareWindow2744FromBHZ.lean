import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalLocalSquareSelector
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth2744
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianSquareWindowD

set_option exponentiation.threshold 3000
/-!
# Actual quantitative square window from exact BHZ + Rhin

No `BHZCriticalInitialSquareBand` is used.

For `P_j ≤ N < P_(j+1)` we identify

  BHZ q_j = P_(j+1).

The exact local selector gives an actual square root

  P_(j+1) ≤ r ≤ 2 P_(j+3).

For `j≥9`, three applications of the existing Rhin degree-14 gap theorem give

  P_(j+3) ≤ C3 * P_j^2744.

Low indices are absorbed by the finite value `P_11`.
Thus the honest currently-proved phase-uniform exponent is 2744.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- finite prefix + Rhin tail を同時に吸収する coefficient。 -/
def criticalSquareWindow2744Constant : ℕ :=
  max
    (2 * criticalPowerP 11)
    (2 * criticalPowerPGapC3)

/-- coefficient positivity。 -/
theorem criticalSquareWindow2744Constant_pos :
    0 < criticalSquareWindow2744Constant := by
  unfold criticalSquareWindow2744Constant
  have hP : 0 < criticalPowerP 11 :=
    criticalPowerP_pos (by omega)
  have hLeft : 0 < 2 * criticalPowerP 11 := by
    positivity
  exact lt_of_lt_of_le hLeft (le_max_left _ _)

/--
Exact BHZ Proposition 3.3 + exact digit admissibility + Rhin から得る actual window。
-/
noncomputable def actualCriticalSturmianSquareWindow2744
    (R : RhinLinearForm14) :
    CriticalSturmianSquareWindow2744 := {
  constant := criticalSquareWindow2744Constant
  constant_pos := criticalSquareWindow2744Constant_pos
  exists_square := by
    intro s N hN
    obtain ⟨j, hjTwo, hPjN, hNPnext⟩ :=
      exists_criticalPowerP_band hN
    let P : CriticalBHZPhasePacket s :=
      actualBHZCriticalCanonicalPacket s
    have hSelector :=
      actualBHZCritical_exists_square_between_q_and_two_q_add_two
        P hjTwo
    rcases hSelector with ⟨r, hQjr, hrQ, hSquare⟩
    have hQj : criticalBHZq j = criticalPowerP (j + 1) := rfl
    have hQj2 : criticalBHZq (j + 2) = criticalPowerP (j + 3) := by
      unfold criticalBHZq
      congr 1
    have hNr : N ≤ r := by
      rw [hQj] at hQjr
      omega
    refine ⟨r, hNr, ?_, hSquare⟩
    rw [hQj2] at hrQ
    by_cases hjNine : 9 ≤ j
    · have hTriple :=
        criticalPowerP_add_three_le_gapC3_mul_pow2744 R hjNine
      have hPow :
          criticalPowerP j ^ 2744 ≤ (N + 1) ^ 2744 := by
        apply Nat.pow_le_pow_left
        omega
      have hTailC :
          2 * criticalPowerPGapC3 ≤
            criticalSquareWindow2744Constant := by
        unfold criticalSquareWindow2744Constant
        exact le_max_right _ _
      calc
        r
            ≤ 2 * criticalPowerP (j + 3) := hrQ
        _ ≤ 2 *
              (criticalPowerPGapC3 * criticalPowerP j ^ 2744) :=
            Nat.mul_le_mul_left 2 hTriple
        _ =
            (2 * criticalPowerPGapC3) * criticalPowerP j ^ 2744 := by
              ring
        _ ≤
            criticalSquareWindow2744Constant * (N + 1) ^ 2744 :=
          Nat.mul_le_mul hTailC hPow
    · have hjLt : j < 9 := by omega
      have hIndexLe : j + 3 ≤ 11 := by omega
      have hFinite :
          criticalPowerP (j + 3) ≤ criticalPowerP 11 :=
        criticalPowerP_mono_from_two (by omega) hIndexLe
      have hFiniteC :
          2 * criticalPowerP 11 ≤ criticalSquareWindow2744Constant := by
        unfold criticalSquareWindow2744Constant
        exact le_max_left _ _
      have hPowOne : 1 ≤ (N + 1) ^ 2744 := by
        have hPos : 0 < (N + 1) ^ 2744 := by
          positivity
        omega
      calc
        r
            ≤ 2 * criticalPowerP (j + 3) := hrQ
        _ ≤ 2 * criticalPowerP 11 :=
            Nat.mul_le_mul_left 2 hFinite
        _ ≤ criticalSquareWindow2744Constant := hFiniteC
        _ = criticalSquareWindow2744Constant * 1 := by simp
        _ ≤ criticalSquareWindow2744Constant * (N + 1) ^ 2744 :=
            Nat.mul_le_mul_left _ hPowOne
}

/-- direct theorem form. -/
theorem exists_actualCriticalSquare_degree2744
    (R : RhinLinearForm14)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      N ≤ r ∧
      r ≤ criticalSquareWindow2744Constant * (N + 1) ^ 2744 ∧
      CriticalBeattySquareAt s r := by
  exact (actualCriticalSturmianSquareWindow2744 R).exists_square s N hN

end ExternalArithmetic
end CSTMicro
end Collatz2
