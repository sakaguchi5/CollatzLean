import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalOneShortSelector
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth2744
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianOneShortSquareWindowD

set_option exponentiation.threshold 300

/-!
# exact BHZ + Rhin から degree 196 one-short window

threshold band

  P_j <= N < P_(j+1)

に対し BHZ indexing は `q_j=P_(j+1)`。
前ファイルの exact selector は

  P_(j+1) <= r <= 2*P_(j+2)

を与える。

従って Rhin の one-step degree 14 growth を二回だけ合成すればよく、
指数は

  14^2 = 196

になる。旧 absolute `C_BHZ` は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- finite prefix と Rhin tail を同時に吸収する coefficient。 -/
def criticalOneShortSquareWindow196Constant : ℕ :=
  max
    (2 * criticalPowerP 10)
    (2 * criticalPowerPGapC2)

/-- coefficient は正。 -/
theorem criticalOneShortSquareWindow196Constant_pos :
    0 < criticalOneShortSquareWindow196Constant := by
  unfold criticalOneShortSquareWindow196Constant
  have hP : 0 < criticalPowerP 10 :=
    criticalPowerP_pos (by omega)
  have hLeft : 0 < 2 * criticalPowerP 10 := by
    positivity
  exact lt_of_lt_of_le hLeft (le_max_left _ _)

/--
actual critical word の phase-uniform degree 196 one-short window。
-/
noncomputable def actualCriticalSturmianOneShortSquareWindow196
    (R : RhinLinearForm14) :
    CriticalSturmianOneShortSquareWindow196 := {
  constant := criticalOneShortSquareWindow196Constant
  constant_pos := criticalOneShortSquareWindow196Constant_pos
  exists_oneShort := by
    intro s N hN
    obtain ⟨j, hjTwo, hPjN, hNPnext⟩ :=
      exists_criticalPowerP_band hN
    let P : CriticalBHZPhasePacket s :=
      actualBHZCriticalCanonicalPacket s
    have hSelector :=
      actualBHZCritical_exists_oneShort_between_q_and_two_q_add_one
        P hjTwo
    rcases hSelector with ⟨r, hQjr, hrQ, hOneShort⟩
    have hQj : criticalBHZq j = criticalPowerP (j + 1) := rfl
    have hQj1 : criticalBHZq (j + 1) = criticalPowerP (j + 2) := by
      unfold criticalBHZq
      congr 1
    have hNr : N ≤ r := by
      rw [hQj] at hQjr
      omega
    refine ⟨r, hNr, ?_, hOneShort⟩
    rw [hQj1] at hrQ
    by_cases hjNine : 9 ≤ j
    · have hDouble :=
        criticalPowerP_add_two_le_gapC2_mul_pow196 R hjNine
      have hPow :
          criticalPowerP j ^ 196 ≤ (N + 1) ^ 196 := by
        apply Nat.pow_le_pow_left
        omega
      have hTailC :
          2 * criticalPowerPGapC2 ≤
            criticalOneShortSquareWindow196Constant := by
        unfold criticalOneShortSquareWindow196Constant
        exact le_max_right _ _
      calc
        r
            ≤ 2 * criticalPowerP (j + 2) := hrQ
        _ ≤ 2 *
              (criticalPowerPGapC2 * criticalPowerP j ^ 196) :=
            Nat.mul_le_mul_left 2 hDouble
        _ =
            (2 * criticalPowerPGapC2) * criticalPowerP j ^ 196 := by
              ring
        _ ≤
            criticalOneShortSquareWindow196Constant * (N + 1) ^ 196 :=
          Nat.mul_le_mul hTailC hPow
    · have hjLt : j < 9 := by omega
      have hIndexLe : j + 2 ≤ 10 := by omega
      have hFinite :
          criticalPowerP (j + 2) ≤ criticalPowerP 10 :=
        criticalPowerP_mono_from_two (by omega) hIndexLe
      have hFiniteC :
          2 * criticalPowerP 10 ≤
            criticalOneShortSquareWindow196Constant := by
        unfold criticalOneShortSquareWindow196Constant
        exact le_max_left _ _
      have hPowOne : 1 ≤ (N + 1) ^ 196 := by
        have hPos : 0 < (N + 1) ^ 196 := by
          positivity
        omega
      calc
        r
            ≤ 2 * criticalPowerP (j + 2) := hrQ
        _ ≤ 2 * criticalPowerP 10 :=
            Nat.mul_le_mul_left 2 hFinite
        _ ≤ criticalOneShortSquareWindow196Constant := hFiniteC
        _ = criticalOneShortSquareWindow196Constant * 1 := by simp
        _ ≤
            criticalOneShortSquareWindow196Constant * (N + 1) ^ 196 :=
          Nat.mul_le_mul_left _ hPowOne
}

/-- theorem 形式の public wrapper。 -/
theorem exists_actualCriticalOneShortSquare_degree196
    (R : RhinLinearForm14)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      N ≤ r ∧
      r ≤ criticalOneShortSquareWindow196Constant * (N + 1) ^ 196 ∧
      CriticalBeattyOneShortSquareAt s r := by
  exact
    (actualCriticalSturmianOneShortSquareWindow196 R).exists_oneShort
      s N hN

end ExternalArithmetic
end CSTMicro
end Collatz2
