import CollatzLean.Collatz3.Bridge.SurvivorCompletionAllStepNormalizedLift
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual value の defect-normalized compact 座標

actual odd-only value を current survivor defect scale で

`V_m = x_m / 2^(δ_m+2)`

と正規化する。

一歩 equation `2^e x' = 3x+1` と

`e_m + δ_(m+1) = δ_m + 1 + s_m`

を合わせると exponent `e_m` が消えて

`V_(m+1) = (3 V_m + 2^(-(δ_m+2))) / 2^(1+s_m)`

となる。

さらに normalized escape coordinate `R_m` とは

`V_m = R_m * 3^m / 2^(beattyIndex m + 2)`

で exact に結ばれ、Beatty lower strict bound から `V_m < R_m/2` を得る。

新しい orbit notion は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- actual odd value を current defect scale `2^(δ+2)` で正規化する。 -/
noncomputable def defectNormalizedActualValue
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℝ :=
  (O.value m : ℝ) /
    (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)

/-- defect-normalized actual value は常に strict に正。 -/
theorem defectNormalizedActualValue_pos
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    0 < O.defectNormalizedActualValue m := by
  unfold defectNormalizedActualValue
  have hxNat : 0 < O.value m := by
    have h := O.one_le_value m
    omega
  have hx : (0 : ℝ) < (O.value m : ℝ) := by exact_mod_cast hxNat
  positivity

/--
actual value の defect-normalized exact recurrence。

`V_(m+1) = (3 V_m + 1/2^(δ_m+2)) / 2^(1+s_m)`。
-/
theorem defectNormalizedActualValue_succ
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.defectNormalizedActualValue (m + 1) =
      (3 * O.defectNormalizedActualValue m +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)) /
        (2 : ℝ) ^ (1 + survivorSturmianStep m) := by
  have hStepNat := (O.step m).equation
  have hStep :
      (2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ) =
        3 * (O.value m : ℝ) + 1 := by
    exact_mod_cast hStepNat
  have hBal :=
    O.exponent_add_nextDefect_eq_defect_add_one_add_sturmianStep SInf m
  let A : ℝ :=
    (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)
  let A' : ℝ :=
    (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent (m + 1) + 2)
  let S : ℝ := (2 : ℝ) ^ (1 + survivorSturmianStep m)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hPow :
      (2 : ℝ) ^ O.exponent m * A' = A * S := by
    dsimp [A, A', S]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  unfold defectNormalizedActualValue
  change (O.value (m + 1) : ℝ) / A' =
    (3 * ((O.value m : ℝ) / A) + 1 / A) / S
  calc
    (O.value (m + 1) : ℝ) / A'
        = ((2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ)) /
            ((2 : ℝ) ^ O.exponent m * A') := by
              field_simp [hA'.ne']
    _ = (3 * (O.value m : ℝ) + 1) / (A * S) := by
          rw [hStep, hPow]
    _ = (3 * ((O.value m : ℝ) / A) + 1 / A) / S := by
          field_simp [hA.ne', hS.ne']

/--
`V_m` と normalized escape `R_m` の exact bridge。

`V_m = R_m * 3^m / 2^(beattyIndex m + 2)`。
-/
theorem defectNormalizedActualValue_eq_escape_mul_threePow_div_beatty
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.defectNormalizedActualValue m =
      O.normalizedEscapeCoordinate m * (3 : ℝ) ^ m /
        (2 : ℝ) ^ (Critical.beattyIndex m + 2) := by
  have hBeatty := beattyIndex_eq_prefixDepth_add_defect SInf m
  unfold defectNormalizedActualValue normalizedEscapeCoordinate
  rw [hBeatty]
  rw [show infinitePrefixDepth O.exponent m +
      infiniteSurvivorDefect O.exponent m + 2 =
      infinitePrefixDepth O.exponent m +
        (infiniteSurvivorDefect O.exponent m + 2) by omega]
  rw [pow_add]
  field_simp
  ring

/--
Beatty strict lower bound により `V_m < R_m/2`。

actual value 側の defect-normalized state は normalized escape state よりさらに compact。
-/
theorem defectNormalizedActualValue_lt_escape_div_two
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.defectNormalizedActualValue m < O.normalizedEscapeCoordinate m / 2 := by
  rw [O.defectNormalizedActualValue_eq_escape_mul_threePow_div_beatty SInf m]
  have hUpperNat := Critical.beattyIndex_upper m
  have hNeNat :
      3 ^ m ≠ 2 ^ (Critical.beattyIndex m + 1) := by
    intro hEq
    rcases threePow_odd_nat m with ⟨q, hq⟩
    rw [hq] at hEq
    rw [pow_succ] at hEq
    have hp := Arithmetic.twoPow_pos (Critical.beattyIndex m)
    omega
  have hStrictNat :
      3 ^ m < 2 ^ (Critical.beattyIndex m + 1) :=
    lt_of_le_of_ne hUpperNat hNeNat
  have hPow :
      (3 : ℝ) ^ m < (2 : ℝ) ^ (Critical.beattyIndex m + 1) := by
    exact_mod_cast hStrictNat
  have hR := O.normalizedEscapeCoordinate_pos m
  have hDen : (0 : ℝ) < (2 : ℝ) ^ (Critical.beattyIndex m + 2) := by positivity
  apply (div_lt_iff₀ hDen).2
  rw [show Critical.beattyIndex m + 2 =
      (Critical.beattyIndex m + 1) + 1 by omega, pow_succ]
  nlinarith

end OddOrbit
end Collatz3
