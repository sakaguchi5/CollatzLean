import CollatzLean.Collatz3.CSTConditional.ACSturmianRefinement
import CollatzLean.Collatz3.Bridge.SurvivorCompletionCenteredResidue
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: future-minimum block Hensel transport

canonical centered completion residue の defining congruence

`3^(m+1) c(m,δ) ≡ -1 (mod 2^(δ+2))`

を二つの時刻で直接比較する。
途中の odd steps を一歩ずつ追わず、block 長 `r` をまとめて消去すると、

* defect flat:
  `3^r sigma_(i+r) = sigma_i + 4 h`,
* defect rise by one:
  `2 * 3^r sigma_(i+r) = sigma_i + 4 h`

を得る。

next-future-minimum transition では Global CST により defect 差は `A/C` と一致するため、

* `A`: rise transport と開始 absolute Sturmian step `1`,
* `C`: flat transport。長さ1なら step `0`、非自明なら既存の `C0/C1` 二分岐

を同じ block theorem 上に載せられる。

新しい alphabet / residue state は導入しない。
-/

namespace Collatz3
namespace Bridge

/-- 2冪 modulus 上で左から掛かった `3^p` を cancel する局所補題。 -/
private theorem cancel_threePow_modEq_block
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
同じ defect scale の二時刻を直接比較した centered residue block relation。
-/
private theorem exists_centeredCompletionCocycleResidue_flat_block_digit
    (i r δ : ℕ) :
    ∃ h : ℤ,
      (3 : ℤ) ^ r * centeredCompletionCocycleResidue (i + r) δ =
        centeredCompletionCocycleResidue i δ +
          (2 : ℤ) ^ (δ + 2) * h := by
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  let ci : ℤ := centeredCompletionCocycleResidue i δ
  let cj : ℤ := centeredCompletionCocycleResidue (i + r) δ
  have hi := centeredCompletionCocycleResidue_spec i δ
  have hj := centeredCompletionCocycleResidue_spec (i + r) δ
  have hj' :
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) ≡
        -1 [ZMOD M] := by
    calc
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) =
          (3 : ℤ) ^ ((i + r) + 1) * cj := by
            rw [show (i + r) + 1 = (i + 1) + r by omega, pow_add]
            ring
      _ ≡ -1 [ZMOD M] := by
            simpa [cj, M] using hj
  have hi' :
      (3 : ℤ) ^ (i + 1) * ci ≡ -1 [ZMOD M] := by
    simpa [ci, M] using hi
  have hEq :
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) ≡
        (3 : ℤ) ^ (i + 1) * ci [ZMOD M] :=
    hj'.trans hi'.symm
  have hCancel :
      (3 : ℤ) ^ r * cj ≡ ci [ZMOD M] := by
    simpa [M] using
      (cancel_threePow_modEq_block
        (p := i + 1) (H := δ + 2) hEq)
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  change (3 : ℤ) ^ r * cj = ci + M * (-q)
  rw [hq]
  ring

/--
defect が1増える二時刻を、開始側 modulus `2^(δ+2)` で直接比較する。
-/
private theorem exists_centeredCompletionCocycleResidue_rise_block_digit
    (i r δ : ℕ) :
    ∃ h : ℤ,
      (3 : ℤ) ^ r * centeredCompletionCocycleResidue (i + r) (δ + 1) =
        centeredCompletionCocycleResidue i δ +
          (2 : ℤ) ^ (δ + 2) * h := by
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  let M2 : ℤ := (2 : ℤ) ^ (δ + 3)
  let ci : ℤ := centeredCompletionCocycleResidue i δ
  let cj : ℤ := centeredCompletionCocycleResidue (i + r) (δ + 1)
  have hi := centeredCompletionCocycleResidue_spec i δ
  have hj := centeredCompletionCocycleResidue_spec (i + r) (δ + 1)
  have hDiv : M ∣ M2 := by
    refine ⟨2, ?_⟩
    dsimp [M, M2]
    rw [show δ + 3 = (δ + 2) + 1 by omega, pow_succ]
  have hjWeak :
      (3 : ℤ) ^ ((i + r) + 1) * cj ≡ -1 [ZMOD M] := by
    have h := hj.of_dvd hDiv
    simpa [cj, M, M2] using h
  have hj' :
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) ≡
        -1 [ZMOD M] := by
    calc
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) =
          (3 : ℤ) ^ ((i + r) + 1) * cj := by
            rw [show (i + r) + 1 = (i + 1) + r by omega, pow_add]
            ring
      _ ≡ -1 [ZMOD M] := hjWeak
  have hi' :
      (3 : ℤ) ^ (i + 1) * ci ≡ -1 [ZMOD M] := by
    simpa [ci, M] using hi
  have hEq :
      (3 : ℤ) ^ (i + 1) * ((3 : ℤ) ^ r * cj) ≡
        (3 : ℤ) ^ (i + 1) * ci [ZMOD M] :=
    hj'.trans hi'.symm
  have hCancel :
      (3 : ℤ) ^ r * cj ≡ ci [ZMOD M] := by
    simpa [M] using
      (cancel_threePow_modEq_block
        (p := i + 1) (H := δ + 2) hEq)
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  change (3 : ℤ) ^ r * cj = ci + M * (-q)
  rw [hq]
  ring

/-- normalized centered residue の flat block transport。 -/
theorem exists_centeredNormalizedCompletionCocycleResidue_flat_block_digit
    (i r δ : ℕ) :
    ∃ h : ℤ,
      (3 : ℝ) ^ r * OddOrbit.centeredNormalizedCompletionCocycleResidue (i + r) δ =
        OddOrbit.centeredNormalizedCompletionCocycleResidue i δ + 4 * (h : ℝ) := by
  rcases exists_centeredCompletionCocycleResidue_flat_block_digit i r δ with
    ⟨h, hh⟩
  refine ⟨h, ?_⟩
  rw [OddOrbit.centeredNormalizedCompletionCocycleResidue_eq_centered_div,
    OddOrbit.centeredNormalizedCompletionCocycleResidue_eq_centered_div]
  have hhR := congrArg (fun z : ℤ => (z : ℝ)) hh
  push_cast at hhR
  have hPow :
      (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    ring
  rw [hPow] at hhR
  field_simp
  nlinarith

/-- normalized centered residue の rise-by-one block transport。 -/
theorem exists_centeredNormalizedCompletionCocycleResidue_rise_block_digit
    (i r δ : ℕ) :
    ∃ h : ℤ,
      2 * (3 : ℝ) ^ r *
          OddOrbit.centeredNormalizedCompletionCocycleResidue (i + r) (δ + 1) =
        OddOrbit.centeredNormalizedCompletionCocycleResidue i δ + 4 * (h : ℝ) := by
  rcases exists_centeredCompletionCocycleResidue_rise_block_digit i r δ with
    ⟨h, hh⟩
  refine ⟨h, ?_⟩
  rw [OddOrbit.centeredNormalizedCompletionCocycleResidue_eq_centered_div,
    OddOrbit.centeredNormalizedCompletionCocycleResidue_eq_centered_div]
  have hhR := congrArg (fun z : ℤ => (z : ℝ)) hh
  push_cast at hhR
  have hPow1 :
      (2 : ℝ) ^ (δ + 1) = 2 * (2 : ℝ) ^ δ := by
    rw [pow_succ]
    ring
  have hPow2 :
      (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
    rw [pow_add]
    norm_num
    ring
  rw [hPow2] at hhR
  rw [hPow1]
  field_simp
  linear_combination hhR

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

/--
`A` next-future-minimum block の centered Hensel transport。

`2 * 3^(j-i) * sigma_j = sigma_i + 4h`。
同時に開始 absolute Sturmian step は `1`。
-/
theorem exists_symbol_A_centeredCompletion_blockTransport_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A) :
    ∃ h : ℤ,
      2 * (3 : ℝ) ^ (j - i) *
          centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j) =
        centeredNormalizedCompletionCocycleResidue
            i (infiniteSurvivorDefect O.exponent i) + 4 * (h : ℝ) ∧
      survivorSturmianStep i = 1 := by
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ SInf hNext).1 hA
  have hIndex : i + (j - i) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  rcases
      exists_centeredNormalizedCompletionCocycleResidue_rise_block_digit
        i (j - i) (infiniteSurvivorDefect O.exponent i) with
    ⟨h, hh⟩
  refine ⟨h, ?_, ?_⟩
  · simpa [hIndex, hRise] using hh
  · exact
      O.nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
        G SInf hStart hNext hA

/--
`C` next-future-minimum block の centered Hensel transport。

`3^(j-i) * sigma_j = sigma_i + 4h`。
-/
theorem exists_symbol_C_centeredCompletion_blockTransport_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C) :
    ∃ h : ℤ,
      (3 : ℝ) ^ (j - i) *
          centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j) =
        centeredNormalizedCompletionCocycleResidue
            i (infiniteSurvivorDefect O.exponent i) + 4 * (h : ℝ) := by
  have hFlat :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i :=
    (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
      G SInf hStart hNext).2 hC
  have hIndex : i + (j - i) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  rcases
      exists_centeredNormalizedCompletionCocycleResidue_flat_block_digit
        i (j - i) (infiniteSurvivorDefect O.exponent i) with
    ⟨h, hh⟩
  refine ⟨h, ?_⟩
  simpa [hIndex, hFlat] using hh

/--
長さ1の `C` は flat Hensel transport と absolute Sturmian step `0` を同時に持つ。
-/
theorem exists_symbol_C_length_one_blockTransport_and_sturmianStep_zero_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLengthOne : j = i + 1) :
    ∃ h : ℤ,
      (3 : ℝ) ^ (j - i) *
          centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j) =
        centeredNormalizedCompletionCocycleResidue
            i (infiniteSurvivorDefect O.exponent i) + 4 * (h : ℝ) ∧
      survivorSturmianStep i = 0 := by
  rcases
      O.exists_symbol_C_centeredCompletion_blockTransport_of_globalCST
        G SInf hStart hNext hC with ⟨h, hh⟩
  refine ⟨h, hh, ?_⟩
  exact O.nextFutureMinimum_symbol_C_length_one_sturmianStep_eq_zero hNext hC hLengthOne

/--
非自明 `C` は flat Hensel transport と既存 `C0/C1` 二分岐を同時に持つ。

新しい `C0/C1` alphabet は作らない。
-/
theorem exists_symbol_C_nontrivial_blockTransport_and_sturmianTail_cases_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLong : i + 1 < j) :
    ∃ h : ℤ,
      (3 : ℝ) ^ (j - i) *
          centeredNormalizedCompletionCocycleResidue
            j (infiniteSurvivorDefect O.exponent j) =
        centeredNormalizedCompletionCocycleResidue
            i (infiniteSurvivorDefect O.exponent i) + 4 * (h : ℝ) ∧
      ((survivorSturmianStep i = 0 ∧
          Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 ∧
          O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1) ∨
        (survivorSturmianStep i = 1 ∧
          Critical.beattyCarry (i + 1) (j - (i + 1)) = 0 ∧
          O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1)) := by
  rcases
      O.exists_symbol_C_centeredCompletion_blockTransport_of_globalCST
        G SInf hStart hNext hC with ⟨h, hh⟩
  refine ⟨h, hh, ?_⟩
  exact
    O.nextFutureMinimum_symbol_C_nontrivial_sturmianTail_cases_of_globalCST
      G SInf hStart hNext hC hLong

end OddOrbit
end Collatz3
