import CollatzLean.Collatz3.Bridge.SurvivorDefectNormalizedActual
import CollatzLean.Collatz3.Canonical.REQ
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual value の defect-scale residue / ordinary quotient

既存の compact state

`V_m = value(m) / 2^(δ_m+2)`

を、同じ自然数 `value(m)` の有限剰余と通常の商に分解する。

* `a_m = value(m) mod 2^(δ_m+2)`
* `k_m = value(m) / 2^(δ_m+2)`
* `θ_m = a_m / 2^(δ_m+2)`

すると exact に

`V_m = k_m + θ_m`, `0 ≤ θ_m < 1`

である。

さらに actual value の `2^n` 剰余は、時刻 `m` から有限 `n` odd steps だけ進んだ
actual segment の canonical start の低位 `n` bits だけで決まる。
従って `a_m` は無限 2進 completion を使わず、有限 future word から exact に復元できる。

新しい orbit structure は導入せず、三つの scalar coordinate だけを置く。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- actual value の current defect-scale residue。 -/
def defectActualResidue
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℕ :=
  O.value m % 2 ^ (infiniteSurvivorDefect O.exponent m + 2)

/-- actual value の current defect-scale ordinary quotient。 -/
def defectActualQuotient
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℕ :=
  O.value m / 2 ^ (infiniteSurvivorDefect O.exponent m + 2)

/-- defect-scale residue を `[0,1)` に正規化した実数座標。 -/
noncomputable def defectActualResidueFraction
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℝ :=
  (O.defectActualResidue m : ℝ) /
    (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)

/--
任意の actual segment では odd-step 数以下の total two-depth を持つ。

各 exponent が正であることだけを使う。
-/
theorem segmentOddSteps_le_twoSteps
    (O : Collatz3.OddOrbit)
    (m n : ℕ) :
    n ≤ Word.twoSteps (O.segmentWord m n) := by
  induction n generalizing m with
  | zero =>
      simp
  | succ n ih =>
      rw [O.segmentWord_succ]
      simp only [Word.twoSteps_cons]
      have he := O.exponent_pos m
      have hTail := ih (m + 1)
      omega

/--
actual value modulo `2^n` は、有限 future segment の canonical start の
低位 `n` bits と exact に一致する。

無限 2進極限は使わない。
-/
theorem value_mod_twoPow_eq_futureCanonicalStart_mod
    (O : Collatz3.OddOrbit)
    (m : ℕ)
    {n : ℕ}
    (hn : 0 < n) :
    O.value m % 2 ^ n =
      Word.canonicalStart (O.segmentWord m n) % 2 ^ n := by
  let w := O.segmentWord m n
  have hne : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps m n
    change Word.oddSteps w = n at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hRun : Runs w (O.value m) (O.value (m + n)) := by
    simpa [w] using O.runsSegment m n
  rcases hRun.exists_canonicalLift hne with ⟨k, hx, _hy⟩
  have hDepth : n ≤ Word.twoSteps w := by
    simpa [w] using O.segmentOddSteps_le_twoSteps m n
  have hExp : n ≤ Word.twoSteps w + 1 := by omega
  have hDvd : 2 ^ n ∣ Word.oddEndpointModulus w := by
    rw [Word.oddEndpointModulus_eq]
    exact Nat.pow_dvd_pow 2 hExp
  rcases hDvd with ⟨q, hq⟩
  have hPeriod : Word.oddEndpointModulus w * k = 2 ^ n * (q * k) := by
    rw [hq]
    ring
  rw [hx, hPeriod, Nat.add_mul_mod_self_left]

/-- current defect-scale residue は有限 future word の canonical start だけで決まる。 -/
theorem defectActualResidue_eq_futureCanonicalStart_mod
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.defectActualResidue m =
      Word.canonicalStart
          (O.segmentWord m (infiniteSurvivorDefect O.exponent m + 2)) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) := by
  unfold defectActualResidue
  exact O.value_mod_twoPow_eq_futureCanonicalStart_mod m (by omega)

/-- residue は modulus 未満。 -/
theorem defectActualResidue_lt_modulus
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.defectActualResidue m <
      2 ^ (infiniteSurvivorDefect O.exponent m + 2) := by
  unfold defectActualResidue
  exact Nat.mod_lt _ (Arithmetic.twoPow_pos _)

/-- normalized residue fraction は `[0,1)` に入る。 -/
theorem defectActualResidueFraction_mem_Ico
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    0 ≤ O.defectActualResidueFraction m ∧
      O.defectActualResidueFraction m < 1 := by
  constructor
  · unfold defectActualResidueFraction
    positivity
  · have hNat := O.defectActualResidue_lt_modulus m
    have hReal :
        (O.defectActualResidue m : ℝ) <
          (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) := by
      exact_mod_cast hNat
    unfold defectActualResidueFraction
    apply (div_lt_iff₀ (by positivity :
      (0 : ℝ) < (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2))).2
    simpa using hReal

/--
actual natural value の quotient/remainder decomposition。

`value = residue + 2^(δ+2) * quotient`。
-/
theorem value_eq_defectActualResidue_add_modulus_mul_quotient
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.value m =
      O.defectActualResidue m +
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) *
          O.defectActualQuotient m := by
  unfold defectActualResidue defectActualQuotient
  exact
    (Nat.mod_add_div (O.value m)
      (2 ^ (infiniteSurvivorDefect O.exponent m + 2))).symm

/--
既存 compact state `V_m` は ordinary quotient と residue fraction に exact 分解する。

`V_m = k_m + θ_m`。
-/
theorem defectNormalizedActualValue_eq_quotient_add_residueFraction
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.defectNormalizedActualValue m =
      (O.defectActualQuotient m : ℝ) +
        O.defectActualResidueFraction m := by
  let M : ℕ := 2 ^ (infiniteSurvivorDefect O.exponent m + 2)
  have hNat := Nat.mod_add_div (O.value m) M
  have hReal :
      ((O.value m % M : ℕ) : ℝ) +
          (M : ℝ) * ((O.value m / M : ℕ) : ℝ) =
        (O.value m : ℝ) := by
    exact_mod_cast hNat
  unfold defectNormalizedActualValue defectActualQuotient
    defectActualResidueFraction defectActualResidue
  dsimp [M] at hReal
  push_cast at hReal
  field_simp
  nlinarith

/-- ordinary quotient は compact state 以下。 -/
theorem defectActualQuotient_le_defectNormalizedActualValue
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    (O.defectActualQuotient m : ℝ) ≤
      O.defectNormalizedActualValue m := by
  rw [O.defectNormalizedActualValue_eq_quotient_add_residueFraction m]
  have hNonneg := (O.defectActualResidueFraction_mem_Ico m).1
  linarith

/--
actual value を「有限 future word が決める residue + ordinary lift」に書いた exact 形。
-/
theorem value_eq_futureCanonicalResidue_add_modulus_mul_quotient
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    O.value m =
      (Word.canonicalStart
          (O.segmentWord m (infiniteSurvivorDefect O.exponent m + 2)) %
        2 ^ (infiniteSurvivorDefect O.exponent m + 2)) +
      2 ^ (infiniteSurvivorDefect O.exponent m + 2) *
        O.defectActualQuotient m := by
  rw [← O.defectActualResidue_eq_futureCanonicalStart_mod m]
  exact O.value_eq_defectActualResidue_add_modulus_mul_quotient m

end OddOrbit
end Collatz3
