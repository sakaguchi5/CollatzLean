import CollatzLean.Collatz3.Bridge.SurvivorDefectActualResidue
import CollatzLean.Collatz3.Bridge.SurvivorCompletionDyadicState
import CollatzLean.Collatz3.Bridge.SurvivorCompletionLift
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual residue と natural completion の finite Hensel compatibility

natural completion lift

`C_m = x_0 + 2^D_m t_m`

に対する既存 endpoint equation

`2^(δ_m+1) Y_m = x_m + 3^m t_m`

だけを使い、actual value と completion lift を同じ有限 modulus
`2^(δ_m+2)` 上で比較する。

中心結果は

`x_m + 3^m t_m ≡ 2^(δ_m+1) (mod 2^(δ_m+2))`

である。`3^m` は modulus と互いに素なので、この有限合同式だけで bounded lift は一意。

さらに実数側では

`V_m + (3^m/4) tau_m = Y_m/2`

を得る。ordinary quotient/remainder decomposition と centered lift
`upsilon=tau-2` を合わせると

`theta_m + (3^m/4) upsilon_m ∈ Z`

となる。

これは real limit と 2進 limit を同一視する主張ではない。
同じ有限 natural endpoint equation の二つの読み方にすぎない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
completion endpoint equation の有限 Hensel congruence。

`x_m + 3^m t ≡ 2^(δ_m+1) (mod 2^(δ_m+2))`。
-/
theorem endpointCompletion_actualHensel_modEq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    O.value m + 3 ^ m * t ≡
      2 ^ (infiniteSurvivorDefect O.exponent m + 1)
      [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] := by
  let d := infiniteSurvivorDefect O.exponent m
  let Y := O.endpointCompletionEnd SInf hm
  have hEnd := O.endpointCompletion_endpoint_eq_of_start_lift SInf hm hStart
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at hEnd
  rcases O.endpointCompletionEnd_odd SInf hm with ⟨q, hq⟩
  have hqY : Y = 2 * q + 1 := by
    simpa [Y] using hq
  have hEq :
      O.value m + 3 ^ m * t =
        2 ^ (d + 1) + 2 ^ (d + 2) * q := by
    calc
      O.value m + 3 ^ m * t = 2 ^ (d + 1) * Y := by
        simpa [d, Y] using hEnd.symm
      _ = 2 ^ (d + 1) * (2 * q + 1) := by
        rw [hqY]
      _ = 2 ^ (d + 1) + 2 ^ (d + 2) * q := by
        rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
        ring
  change
    (O.value m + 3 ^ m * t) % 2 ^ (d + 2) =
      2 ^ (d + 1) % 2 ^ (d + 2)
  rw [hEq, Nat.add_mul_mod_self_left]

/--
同じ Hensel congruence を actual residue `a_m = x_m mod 2^(δ_m+2)` だけで書いた形。

従って completion lift の有限条件に必要な actual 側情報は `a_m` だけである。
-/
theorem endpointCompletion_actualResidueHensel_modEq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    O.defectActualResidue m + 3 ^ m * t ≡
      2 ^ (infiniteSurvivorDefect O.exponent m + 1)
      [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] := by
  have h := O.endpointCompletion_actualHensel_modEq SInf hm hStart
  change
    (O.defectActualResidue m + 3 ^ m * t) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) =
      2 ^ (infiniteSurvivorDefect O.exponent m + 1) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2)
  change
    (O.value m + 3 ^ m * t) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) =
      2 ^ (infiniteSurvivorDefect O.exponent m + 1) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) at h
  unfold defectActualResidue
  simpa [Nat.add_mod] using h

/--
Hensel congruence の actual residue を有限 future word の canonical start に置き換えた形。

従って bounded natural completion lift は、有限 future word が与える低位 bits と
有限 modulus の合同式だけで制約される。
-/
theorem endpointCompletion_futureCanonicalResidueHensel_modEq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    (Word.canonicalStart
        (O.segmentWord m (infiniteSurvivorDefect O.exponent m + 2)) %
      2 ^ (infiniteSurvivorDefect O.exponent m + 2)) +
        3 ^ m * t ≡
      2 ^ (infiniteSurvivorDefect O.exponent m + 1)
      [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] := by
  rw [← O.defectActualResidue_eq_futureCanonicalStart_mod m]
  exact O.endpointCompletion_actualResidueHensel_modEq SInf hm hStart

/--
同じ actual `x_m` に対する Hensel congruence の二解は modulo `2^(δ+2)` で一致する。

`3^m` が 2冪 modulus と互いに素であることだけを使う。
-/
theorem actualHenselLift_modEq_unique
    (O : Collatz3.OddOrbit)
    (m t u : ℕ)
    (ht :
      O.value m + 3 ^ m * t ≡
        2 ^ (infiniteSurvivorDefect O.exponent m + 1)
        [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)])
    (hu :
      O.value m + 3 ^ m * u ≡
        2 ^ (infiniteSurvivorDefect O.exponent m + 1)
        [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)]) :
    t ≡ u [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] := by
  have hSum := ht.trans hu.symm
  have hMul :
      3 ^ m * t ≡ 3 ^ m * u
        [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] :=
    Nat.ModEq.add_left_cancel' (O.value m) hSum
  have hGcd :
      Nat.gcd
        (2 ^ (infiniteSurvivorDefect O.exponent m + 2))
        (3 ^ m) = 1 :=
    (Arithmetic.coprime_threePow_twoPow
      m (infiniteSurvivorDefect O.exponent m + 2)).symm
  exact hMul.cancel_left_of_coprime hGcd

/-- bounded Hensel lift は自然数として一意。 -/
theorem actualHenselLift_unique_of_lt_modulus
    (O : Collatz3.OddOrbit)
    (m t u : ℕ)
    (htEq :
      O.value m + 3 ^ m * t ≡
        2 ^ (infiniteSurvivorDefect O.exponent m + 1)
        [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)])
    (huEq :
      O.value m + 3 ^ m * u ≡
        2 ^ (infiniteSurvivorDefect O.exponent m + 1)
        [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)])
    (ht : t < 2 ^ (infiniteSurvivorDefect O.exponent m + 2))
    (hu : u < 2 ^ (infiniteSurvivorDefect O.exponent m + 2)) :
    t = u := by
  have h := O.actualHenselLift_modEq_unique m t u htEq huEq
  change
    t % 2 ^ (infiniteSurvivorDefect O.exponent m + 2) =
      u % 2 ^ (infiniteSurvivorDefect O.exponent m + 2) at h
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hu] at h
  exact h

/--
finite endpoint equation を defect-normalized real coordinates へ移した exact identity。

`V_m + (3^m/4) tau_m = Y_m/2`。
-/
theorem defectNormalizedActual_add_scaledCompletionLift_eq_half_endpoint
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    O.defectNormalizedActualValue m +
        ((3 : ℝ) ^ m / 4) * O.normalizedCompletionLiftCoefficient m t =
      (O.endpointCompletionEnd SInf hm : ℝ) / 2 := by
  let d := infiniteSurvivorDefect O.exponent m
  let Y := O.endpointCompletionEnd SInf hm
  have hEndNat := O.endpointCompletion_endpoint_eq_of_start_lift SInf hm hStart
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at hEndNat
  have hEnd :
      (2 : ℝ) ^ (d + 1) * (Y : ℝ) =
        (O.value m : ℝ) + (3 : ℝ) ^ m * (t : ℝ) := by
    exact_mod_cast hEndNat
  unfold defectNormalizedActualValue normalizedCompletionLiftCoefficient
  dsimp [d, Y] at hEnd ⊢
  calc
    (O.value m : ℝ) /
          (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) +
        ((3 : ℝ) ^ m / 4) *
          ((t : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
        =
      ((O.value m : ℝ) + (3 : ℝ) ^ m * (t : ℝ)) /
        (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) := by
          rw [show infiniteSurvivorDefect O.exponent m + 2 =
              infiniteSurvivorDefect O.exponent m + 2 by rfl]
          rw [pow_add]
          norm_num
          field_simp
    _ =
      ((2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 1) *
          (O.endpointCompletionEnd SInf hm : ℝ)) /
        (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) := by
          rw [← hEnd]
    _ = (O.endpointCompletionEnd SInf hm : ℝ) / 2 := by
          rw [show infiniteSurvivorDefect O.exponent m + 2 =
              (infiniteSurvivorDefect O.exponent m + 1) + 1 by omega,
            pow_succ]
          field_simp
          ring

/--
actual residue fraction と centered completion lift の finite integer compatibility。

`theta_m + (3^m/4) upsilon_m` は整数。
-/
theorem exists_integer_defectActualResidueFraction_add_scaled_centeredLift
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ∃ z : ℤ,
      O.defectActualResidueFraction m +
          ((3 : ℝ) ^ m / 4) *
            O.centeredNormalizedCompletionLiftCoefficient m t =
        (z : ℝ) := by
  have hHalf :=
    O.defectNormalizedActual_add_scaledCompletionLift_eq_half_endpoint
      SInf hm hStart
  rw [O.defectNormalizedActualValue_eq_quotient_add_residueFraction m] at hHalf
  rcases O.endpointCompletionEnd_odd SInf hm with ⟨a, ha⟩
  rcases threePow_odd_nat m with ⟨b, hb⟩
  let q := O.defectActualQuotient m
  refine ⟨(a : ℤ) - (b : ℤ) - (q : ℤ), ?_⟩
  have haR :
      (O.endpointCompletionEnd SInf hm : ℝ) = 2 * (a : ℝ) + 1 := by
    exact_mod_cast ha
  have hbR : (3 : ℝ) ^ m = 2 * (b : ℝ) + 1 := by
    exact_mod_cast hb
  unfold centeredNormalizedCompletionLiftCoefficient
  dsimp [q]
  push_cast
  ring_nf at hHalf ⊢
  nlinarith [haR, hbR]

/-- dyadic state の定義を centered lift について解いた形。 -/
theorem centeredCompletionLift_eq_four_mul_dyadicState_sub_three_sigma
    (O : Collatz3.OddOrbit)
    (m t : ℕ) :
    O.centeredNormalizedCompletionLiftCoefficient m t =
      4 * O.normalizedCompletionDyadicState m t -
        3 * centeredNormalizedCompletionCocycleResidue
          m (infiniteSurvivorDefect O.exponent m) := by
  unfold normalizedCompletionDyadicState
  ring

/--
finite compatibility を dyadic state `xi` と centered canonical residue `sigma` で書いた形。

`theta_m + 3^m xi_m - (3^(m+1)/4) sigma_m ∈ Z`。
-/
theorem exists_integer_defectActualResidueFraction_add_dyadicState_sub_sigma
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ∃ z : ℤ,
      O.defectActualResidueFraction m +
          (3 : ℝ) ^ m * O.normalizedCompletionDyadicState m t -
          ((3 : ℝ) ^ (m + 1) / 4) *
            centeredNormalizedCompletionCocycleResidue
              m (infiniteSurvivorDefect O.exponent m) =
        (z : ℝ) := by
  rcases
      O.exists_integer_defectActualResidueFraction_add_scaled_centeredLift
        SInf hm hStart with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hU := O.centeredCompletionLift_eq_four_mul_dyadicState_sub_three_sigma m t
  rw [hU] at hz
  rw [pow_succ]
  ring_nf at hz ⊢
  exact hz

end OddOrbit
end Collatz3
