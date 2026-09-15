import CollatzLean.Collatz3.CSTConditional.FutureMinimumDefectExact
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionGridSeparation
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: future-minimum integral completion lattice

既存の finite compatibility

`theta_m + 3^m xi_m - (3^(m+1)/4) sigma_m ∈ Z`

と centered canonical residue の defining congruence

`3^(m+1) c(m,δ) ≡ -1 (mod 2^(δ+2))`

を足し合わせる。

すると natural completion が存在する任意の endpoint で

`theta_m + 2^(-(δ_m+2)) + 3^m xi_m ∈ Z`

を得る。

さらに `m` が actual future minimum なら exponent は `1` で、actual residue は
`3 mod 4`。dyadic state の整数分子をこの合同条件と合わせると 4 が約分でき、

`xi_m = Z_m / 2^δ_m`

まで格子を粗くできる。同じ整数 compatibility は

`(a_m+1)/4 + 3^m Z_m ≡ 0 (mod 2^δ_m)`

となる。

新しい real state / residue / profile は定義しない。
-/

namespace Collatz3
namespace Bridge

/-- 2冪 modulus 上で `3^p` を cancel する局所補題。 -/
theorem cancel_threePow_modEq_lattice
    {p H : ℕ}
    {a b : ℤ}
    (h :
      (3 : ℤ) ^ p * a ≡ (3 : ℤ) ^ p * b
        [ZMOD (2 : ℤ) ^ H]) :
    a ≡ b [ZMOD (2 : ℤ) ^ H] := by
  rcases Int.mod_coprime (Arithmetic.coprime_threePow_twoPow p H) with
    ⟨y, hy⟩
  have hy' :
      (3 : ℤ) ^ p * y ≡ 1 [ZMOD (2 : ℤ) ^ H] := by
    simpa using hy
  have hMul := h.mul_left y
  have hya := hy'.mul_right a
  have hyb := hy'.mul_right b
  have hMul' :
      ((3 : ℤ) ^ p * y) * a ≡
        ((3 : ℤ) ^ p * y) * b
        [ZMOD (2 : ℤ) ^ H] := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hMul
  simpa using hya.symm.trans (hMul'.trans hyb)

/--
centered canonical residue が作る補正項は `2^(-(δ+2))` を足すと整数になる。
-/
theorem exists_integer_scaled_centeredCompletionResidue_add_epsilon
    (m δ : ℕ) :
    ∃ z : ℤ,
      ((3 : ℝ) ^ (m + 1) / 4) *
          OddOrbit.centeredNormalizedCompletionCocycleResidue m δ +
        1 / (2 : ℝ) ^ (δ + 2) =
      (z : ℝ) := by
  have hSpec := centeredCompletionCocycleResidue_spec m δ
  rcases Int.modEq_iff_add_fac.mp hSpec with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  rw [OddOrbit.centeredNormalizedCompletionCocycleResidue_eq_centered_div]
  have hqR := congrArg (fun z : ℤ => (z : ℝ)) hq
  push_cast at hqR
  have hPow :
      (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    ring
  rw [hPow] at hqR ⊢
  field_simp
  push_cast
  linear_combination -hqR

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

/--
finite actual/completion compatibility と centered residue congruence の和。

`theta + 2^(-(δ+2)) + 3^m xi` は整数。
-/
theorem exists_integer_defectActualResidueFraction_add_epsilon_add_dyadicState
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ∃ z : ℤ,
      O.defectActualResidueFraction m +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) +
          (3 : ℝ) ^ m * O.normalizedCompletionDyadicState m t =
        (z : ℝ) := by
  rcases
      O.exists_integer_defectActualResidueFraction_add_dyadicState_sub_sigma
        SInf hm hStart with ⟨z₁, hz₁⟩
  rcases
      exists_integer_scaled_centeredCompletionResidue_add_epsilon
        m (infiniteSurvivorDefect O.exponent m) with ⟨z₂, hz₂⟩
  refine ⟨z₁ + z₂, ?_⟩
  push_cast
  nlinarith [hz₁, hz₂]

/--
exponent `1` の actual odd step の始点は `3 mod 4`。
-/
theorem value_mod_four_eq_three_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    {m : ℕ}
    (he : O.exponent m = 1) :
    O.value m % 4 = 3 := by
  have hStep := O.step m
  have hEq := hStep.equation
  rw [he] at hEq
  norm_num at hEq
  rcases hStep.start_odd with ⟨p, hp⟩
  rcases hStep.end_odd with ⟨q, hq⟩
  obtain ⟨k, hk | hk⟩ := p.even_or_odd'
  · rw [hp, hq, hk] at hEq
    omega
  · have hx : O.value m = 4 * k + 3 := by
      rw [hp, hk]
      omega
    rw [hx]
    omega

/-- future minimum の defect-scale actual residue も `3 mod 4`。 -/
theorem futureMinimum_defectActualResidue_mod_four_eq_three
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hMin : O.FutureMinimumAt m) :
    O.defectActualResidue m % 4 = 3 := by
  have he : O.exponent m = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor SInf hMin
  have hx := O.value_mod_four_eq_three_of_exponent_eq_one he
  have hDvd : 4 ∣ 2 ^ (infiniteSurvivorDefect O.exponent m + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 (by omega)
  unfold defectActualResidue
  rw [Nat.mod_mod_of_dvd _ hDvd]
  exact hx

/--
dyadic state は常に `4 * 2^δ` 格子上にある。

future-minimum 条件を使う前の純粋な定義展開。
-/
theorem exists_integer_dyadicState_quarterGrid
    (O : Collatz3.OddOrbit)
    (m t : ℕ) :
    ∃ N : ℤ,
      O.normalizedCompletionDyadicState m t =
        (N : ℝ) /
          (4 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m) := by
  let δ := infiniteSurvivorDefect O.exponent m
  let c : ℤ := centeredCompletionCocycleResidue m δ
  refine ⟨(t : ℤ) - (2 : ℤ) ^ (δ + 1) + 3 * c, ?_⟩
  unfold normalizedCompletionDyadicState
    centeredNormalizedCompletionLiftCoefficient
    normalizedCompletionLiftCoefficient
  rw [centeredNormalizedCompletionCocycleResidue_eq_centered_div]
  dsimp [δ, c]
  push_cast
  rw [pow_succ]
  field_simp

/--
future minimum では quarter-grid の整数分子が 4 の倍数になる。

従って `xi = Z / 2^δ` へ exact に約分できる。
-/
theorem exists_futureMinimum_dyadicState_defectGrid
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hMin : O.FutureMinimumAt m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ∃ Z : ℤ,
      O.normalizedCompletionDyadicState m t =
        (Z : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m ∧
      (((O.defectActualResidue m + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ m * Z ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent m] := by
  let δ := infiniteSurvivorDefect O.exponent m
  let a := O.defectActualResidue m
  rcases O.exists_integer_dyadicState_quarterGrid m t with ⟨N, hXi⟩
  rcases
      O.exists_integer_defectActualResidueFraction_add_epsilon_add_dyadicState
        SInf hm hStart with ⟨z, hz⟩
  have haMod : a % 4 = 3 := by
    simpa [a] using O.futureMinimum_defectActualResidue_mod_four_eq_three SInf hMin
  have haDecomp : a + 1 = 4 * ((a + 1) / 4) := by
    omega
  have hPowReal :
      (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    ring
  have hEqR :
      (a : ℝ) + 1 + (3 : ℝ) ^ m * (N : ℝ) =
        4 * (2 : ℝ) ^ δ * (z : ℝ) := by
    change
      (a : ℝ) / (2 : ℝ) ^ (δ + 2) +
          1 / (2 : ℝ) ^ (δ + 2) +
          (3 : ℝ) ^ m * O.normalizedCompletionDyadicState m t =
        (z : ℝ) at hz
    change
      O.normalizedCompletionDyadicState m t =
        (N : ℝ) / (4 * (2 : ℝ) ^ δ) at hXi
    rw [hXi, hPowReal] at hz
    field_simp at hz
    nlinarith
  have hEqZ :
      (a : ℤ) + 1 + (3 : ℤ) ^ m * N =
        4 * (2 : ℤ) ^ δ * z := by
    exact_mod_cast hEqR
  have haDecompZ :
      (a : ℤ) + 1 = 4 * (((a + 1) / 4 : ℕ) : ℤ) := by
    exact_mod_cast haDecomp
  have hMulEq :
      (3 : ℤ) ^ m * N =
        4 * ((2 : ℤ) ^ δ * z - (((a + 1) / 4 : ℕ) : ℤ)) := by
    calc
      (3 : ℤ) ^ m * N =
          ((a : ℤ) + 1 + (3 : ℤ) ^ m * N) - ((a : ℤ) + 1) := by ring
      _ =
          4 * (2 : ℤ) ^ δ * z -
            4 * (((a + 1) / 4 : ℕ) : ℤ) := by rw [hEqZ, haDecompZ]
      _ =
          4 * ((2 : ℤ) ^ δ * z - (((a + 1) / 4 : ℕ) : ℤ)) := by ring
  have hMulMod :
      (3 : ℤ) ^ m * N ≡ (3 : ℤ) ^ m * 0
        [ZMOD (2 : ℤ) ^ 2] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-((2 : ℤ) ^ δ * z - (((a + 1) / 4 : ℕ) : ℤ)), ?_⟩
    rw [hMulEq]
    norm_num
    ring
  have hNMod : N ≡ 0 [ZMOD (2 : ℤ) ^ 2] :=
    Bridge.cancel_threePow_modEq_lattice hMulMod
  rcases Int.modEq_iff_add_fac.mp hNMod with ⟨q, hq⟩
  let Z : ℤ := -q
  have hN : N = 4 * Z := by
    dsimp [Z]
    norm_num at hq ⊢
    linarith
  refine ⟨Z, ?_, ?_⟩
  · rw [hXi, hN]
    field_simp
    ring_nf
    simp
  · apply Int.modEq_iff_dvd.2
    refine ⟨-z, ?_⟩
    rw [haDecompZ, hN] at hEqZ
    have hFour :
        (4 : ℤ) *
            ((((a + 1) / 4 : ℕ) : ℤ) + (3 : ℤ) ^ m * Z) =
          4 * ((2 : ℤ) ^ δ * z) := by
      calc
        (4 : ℤ) *
              ((((a + 1) / 4 : ℕ) : ℤ) + (3 : ℤ) ^ m * Z) =
            4 * (((a + 1) / 4 : ℕ) : ℤ) +
              (3 : ℤ) ^ m * (4 * Z) := by ring
        _ = 4 * (2 : ℤ) ^ δ * z := hEqZ
        _ = 4 * ((2 : ℤ) ^ δ * z) := by ring
    have hReduced :
        (((a + 1) / 4 : ℕ) : ℤ) + (3 : ℤ) ^ m * Z =
          (2 : ℤ) ^ δ * z := by
      nlinarith [hFour]
    rw [hReduced]
    ring

/--
bounded natural completion では future-minimum defect-grid point は `(-2,2)` 内にある。

従って fixed `m,δ` では候補は有限個の整数格子点に落ちる。
-/
theorem exists_futureMinimum_dyadicState_bounded_defectGrid
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hMin : O.FutureMinimumAt m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (htPos : 0 < t)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1)) :
    ∃ Z : ℤ,
      O.normalizedCompletionDyadicState m t =
        (Z : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m ∧
      -2 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m < (Z : ℝ) ∧
      (Z : ℝ) < 2 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
  rcases
      O.exists_futureMinimum_dyadicState_defectGrid
        SInf hm hMin hStart with ⟨Z, hXi, _hCong⟩
  have hU :=
    O.centeredNormalizedCompletionLiftCoefficient_mem_Ioo SInf htPos ht
  have hS :=
    centeredNormalizedCompletionCocycleResidue_mem_Ico
      m (infiniteSurvivorDefect O.exponent m)
  have hXiBound :
      -2 < O.normalizedCompletionDyadicState m t ∧
        O.normalizedCompletionDyadicState m t < 2 := by
    unfold normalizedCompletionDyadicState
    constructor <;> nlinarith
  refine ⟨Z, hXi, ?_, ?_⟩
  · rw [hXi] at hXiBound
    have hPos :
        (0 : ℝ) < (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
      positivity
    exact (lt_div_iff₀ hPos).1 hXiBound.1
  · rw [hXi] at hXiBound
    have hPos :
        (0 : ℝ) < (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
      positivity
    exact (div_lt_iff₀ hPos).1 hXiBound.2

end OddOrbit
end Collatz3
