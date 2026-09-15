import CollatzLean.Collatz3.Bridge.SurvivorCompletionNormalizedLift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: normalized completion lift の全-step recurrence

future-minimum `e_m=1` に限らず、任意の survivor step について

`q_m = 2^(e_m) t_(m+1) - t_m`

を current defect scale `2^δ_m` で割る。

既存 exact balance

`e_m + E_(m+1) = E_m + (1+s_m)`

と `E_m=δ_m+1` から

`e_m + δ_(m+1) = δ_m + 1 + s_m`

を得る。したがって exponent `e_m` は normalized recurrence から消え、

`q_m / 2^δ_m = 2^(1+s_m) tau_(m+1) - tau_m`

となる。

新しい completion state は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
actual exponent・next defect・current defect・Sturmian step の exact balance。

`e_m + δ_(m+1) = δ_m + 1 + s_m`。
-/
theorem exponent_add_nextDefect_eq_defect_add_one_add_sturmianStep
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.exponent m + infiniteSurvivorDefect O.exponent (m + 1) =
      infiniteSurvivorDefect O.exponent m + 1 + survivorSturmianStep m := by
  have h := O.endpointCompletionExtraDepth_balance SInf m
  rw [
    O.endpointCompletionExtraDepth_eq_defect_add_one SInf m,
    O.endpointCompletionExtraDepth_eq_defect_add_one SInf (m + 1)
  ] at h
  unfold completionCriticalStep at h
  omega

/--
全 step に対する normalized lift recurrence。

`q_m / 2^δ_m = 2^(1+s_m) tau_(m+1) - tau_m`。
-/
theorem normalizedCompletionLiftStep_eq_sturmianScale_mul_sub
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m t u : ℕ) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
      (2 : ℝ) ^ (1 + survivorSturmianStep m) *
          O.normalizedCompletionLiftCoefficient (m + 1) u -
        O.normalizedCompletionLiftCoefficient m t := by
  have hBal :=
    O.exponent_add_nextDefect_eq_defect_add_one_add_sturmianStep SInf m
  unfold endpointCompletionLiftStep normalizedCompletionLiftCoefficient
  push_cast
  have hPow :
      (2 : ℝ) ^ O.exponent m *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1) =
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m *
          (2 : ℝ) ^ (1 + survivorSturmianStep m) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  field_simp
  calc
    ((2 : ℝ) ^ O.exponent m * (u : ℝ) - (t : ℝ)) *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1)
        =
      (u : ℝ) *
          ((2 : ℝ) ^ O.exponent m *
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1)) -
        (t : ℝ) *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1) := by
            ring
    _ =
      (u : ℝ) *
          ((2 : ℝ) ^ infiniteSurvivorDefect O.exponent m *
            (2 : ℝ) ^ (1 + survivorSturmianStep m)) -
        (t : ℝ) *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1) := by
            rw [hPow]
    _ =
      (u : ℝ) *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m *
          (2 : ℝ) ^ (1 + survivorSturmianStep m) -
        (t : ℝ) *
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent (m + 1) := by
            ring

/-- Sturmian step `0` なら全-step normalized recurrence の係数は `2`。 -/
theorem normalizedCompletionLiftStep_eq_two_mul_sub_of_sturmianStep_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hs : survivorSturmianStep m = 0) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
      2 * O.normalizedCompletionLiftCoefficient (m + 1) u -
        O.normalizedCompletionLiftCoefficient m t := by
  have h := O.normalizedCompletionLiftStep_eq_sturmianScale_mul_sub SInf m t u
  rw [hs] at h
  norm_num at h ⊢
  exact h

/-- Sturmian step `1` なら全-step normalized recurrence の係数は `4`。 -/
theorem normalizedCompletionLiftStep_eq_four_mul_sub_of_sturmianStep_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hs : survivorSturmianStep m = 1) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
      4 * O.normalizedCompletionLiftCoefficient (m + 1) u -
        O.normalizedCompletionLiftCoefficient m t := by
  have h := O.normalizedCompletionLiftStep_eq_sturmianScale_mul_sub SInf m t u
  rw [hs] at h
  norm_num at h ⊢
  exact h

end OddOrbit
end Collatz3
