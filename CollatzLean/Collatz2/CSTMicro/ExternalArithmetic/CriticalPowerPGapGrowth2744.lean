import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth14

/-!
# Three-step actual P-growth from Rhin

one-step theorem

  P_(j+1) ≤ 32768 * P_j^14

を三回合成する。
BHZ local selector が threshold band の直後から最大二つ先の BHZ denominator
`q_(j+2)` まで見るため、repository P-index では `P_(j+3)` が必要になる。

結果の exponent は

  14^3 = 2744.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- one-step coefficient。 -/
def criticalPowerPGapC1 : ℕ := 32768

/-- two-step coefficient。 -/
def criticalPowerPGapC2 : ℕ :=
  criticalPowerPGapC1 * criticalPowerPGapC1 ^ 14

/-- three-step coefficient。 -/
def criticalPowerPGapC3 : ℕ :=
  criticalPowerPGapC1 * criticalPowerPGapC2 ^ 14

/-- two consecutive Rhin P-growth steps: exponent `14^2=196`。 -/
theorem criticalPowerP_add_two_le_gapC2_mul_pow196
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalPowerP (j + 2) ≤
      criticalPowerPGapC2 * criticalPowerP j ^ 196 := by
  have h1 :=
    criticalPowerP_next_le_32768_mul_pow14 R (j := j) hj
  have h2 :=
    criticalPowerP_next_le_32768_mul_pow14 R
      (j := j + 1) (by omega)
  have hPow :
      criticalPowerP (j + 1) ^ 14 ≤
        (criticalPowerPGapC1 * criticalPowerP j ^ 14) ^ 14 := by
    apply Nat.pow_le_pow_left
    simpa [criticalPowerPGapC1] using h1
  calc
    criticalPowerP (j + 2)
        ≤ criticalPowerPGapC1 * criticalPowerP (j + 1) ^ 14 := by
          simpa [criticalPowerPGapC1, Nat.add_assoc] using h2
    _ ≤ criticalPowerPGapC1 *
          (criticalPowerPGapC1 * criticalPowerP j ^ 14) ^ 14 :=
        Nat.mul_le_mul_left _ hPow
    _ = criticalPowerPGapC2 * criticalPowerP j ^ 196 := by
        unfold criticalPowerPGapC2
        rw [mul_pow]
        rw [← pow_mul]
        norm_num
        ring

/-- three consecutive Rhin P-growth steps: exponent `14^3=2744`。 -/
theorem criticalPowerP_add_three_le_gapC3_mul_pow2744
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalPowerP (j + 3) ≤
      criticalPowerPGapC3 * criticalPowerP j ^ 2744 := by
  have h2 :=
    criticalPowerP_add_two_le_gapC2_mul_pow196 R hj
  have hNext :=
    criticalPowerP_next_le_32768_mul_pow14 R
      (j := j + 2) (by omega)
  have hPow :
      criticalPowerP (j + 2) ^ 14 ≤
        (criticalPowerPGapC2 * criticalPowerP j ^ 196) ^ 14 := by
    exact Nat.pow_le_pow_left h2 14
  calc
    criticalPowerP (j + 3)
        ≤ criticalPowerPGapC1 * criticalPowerP (j + 2) ^ 14 := by
          simpa [criticalPowerPGapC1, Nat.add_assoc] using hNext
    _ ≤ criticalPowerPGapC1 *
          (criticalPowerPGapC2 * criticalPowerP j ^ 196) ^ 14 :=
        Nat.mul_le_mul_left _ hPow
    _ = criticalPowerPGapC3 * criticalPowerP j ^ 2744 := by
        unfold criticalPowerPGapC3
        rw [mul_pow]
        rw [← pow_mul]
        norm_num
        ring

end ExternalArithmetic
end CSTMicro
end Collatz2
