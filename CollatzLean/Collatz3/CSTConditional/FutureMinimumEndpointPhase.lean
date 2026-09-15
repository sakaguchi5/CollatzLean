import CollatzLean.Collatz3.CSTConditional.FutureMinimumXiCorrectionUniqueness
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: defect-grid branch と endpoint mod 8 位相

future-minimum defect-grid では

`xi = Z / 2^δ`

という整数格子表現がある。ただし同じ canonical completion に複数の lift があるわけではない。
canonical natural lift 自体は既存 theorem により一意である。

ここでは **代数的な格子候補** を比較する。
同じ幅 `m` で

`Z₂ = Z₁ + 2^δ k`

と格子を `k` 本ずらすと、dyadic state の定義だけから normalized lift は `4k` 動き、
自然数 lift coefficient は

`t₂ = t₁ + 4 * 2^δ * k`

だけ動く。

さらに二つの affine endpoint 候補が

`2^(δ+1) Y = x_m + 3^m t`

を満たすなら

`Y₂ = Y₁ + 2 * 3^m * k`

となる。従って endpoint の modulo `8` 位相は branch index modulo `4` を識別する。

新しい phase 型・branch 型・state structure は導入しない。
既存 `xi`, integer grid, affine endpoint equation だけの derived theorem として保存する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
同じ幅 `m` の defect-grid 表現を `k` 格子分ずらすと、
natural lift coefficient は `4 * 2^δ * k` だけずれる。

これは canonical lift が複数存在するという主張ではなく、
`xi` の代数的格子候補間の exact relation である。
-/
theorem dyadicState_defectGridShift_implies_liftShift
    (O : Collatz3.OddOrbit)
    (m t₁ t₂ k : ℕ)
    (Z₁ Z₂ : ℤ)
    (hXi₁ :
      O.normalizedCompletionDyadicState m t₁ =
        (Z₁ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
    (hXi₂ :
      O.normalizedCompletionDyadicState m t₂ =
        (Z₂ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
    (hZ :
      Z₂ = Z₁ +
        (2 : ℤ) ^ infiniteSurvivorDefect O.exponent m * (k : ℤ)) :
    t₂ = t₁ +
      4 * 2 ^ infiniteSurvivorDefect O.exponent m * k := by
  let δ := infiniteSurvivorDefect O.exponent m
  have hXiShift :
      O.normalizedCompletionDyadicState m t₂ =
        O.normalizedCompletionDyadicState m t₁ + (k : ℝ) := by
    rw [hXi₂, hXi₁, hZ]
    push_cast
    field_simp
  have hU₁ :=
    O.centeredCompletionLift_eq_four_mul_dyadicState_sub_three_sigma m t₁
  have hU₂ :=
    O.centeredCompletionLift_eq_four_mul_dyadicState_sub_three_sigma m t₂
  have hCenteredShift :
      O.centeredNormalizedCompletionLiftCoefficient m t₂ =
        O.centeredNormalizedCompletionLiftCoefficient m t₁ + 4 * (k : ℝ) := by
    rw [hXiShift] at hU₂
    nlinarith [hU₁, hU₂]
  unfold centeredNormalizedCompletionLiftCoefficient at hCenteredShift
  have hTauShift :
      O.normalizedCompletionLiftCoefficient m t₂ =
        O.normalizedCompletionLiftCoefficient m t₁ + 4 * (k : ℝ) := by
    linarith
  unfold normalizedCompletionLiftCoefficient at hTauShift
  have htR :
      (t₂ : ℝ) =
        (t₁ : ℝ) +
          4 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m * (k : ℝ) := by
    field_simp at hTauShift
    nlinarith [hTauShift]
  exact_mod_cast htR

/--
同じ actual value `x_m` に対する二つの affine endpoint 候補を比較する。

lift が `4 * 2^δ * k` だけ動けば endpoint は exact に
`2 * 3^m * k` だけ動く。
-/
theorem affineEndpointCandidate_shift_of_liftGridShift
    (O : Collatz3.OddOrbit)
    (m δ t₁ t₂ Y₁ Y₂ k : ℕ)
    (ht : t₂ = t₁ + 4 * 2 ^ δ * k)
    (hY₁ :
      2 ^ (δ + 1) * Y₁ = O.value m + 3 ^ m * t₁)
    (hY₂ :
      2 ^ (δ + 1) * Y₂ = O.value m + 3 ^ m * t₂) :
    Y₂ = Y₁ + 2 * 3 ^ m * k := by
  have hMul :
      2 ^ (δ + 1) * Y₂ =
        2 ^ (δ + 1) * (Y₁ + 2 * 3 ^ m * k) := by
    calc
      2 ^ (δ + 1) * Y₂
          = O.value m + 3 ^ m * t₂ := hY₂
      _ = O.value m + 3 ^ m * (t₁ + 4 * 2 ^ δ * k) := by rw [ht]
      _ = (O.value m + 3 ^ m * t₁) +
            3 ^ m * (4 * 2 ^ δ * k) := by ring
      _ = 2 ^ (δ + 1) * Y₁ +
            3 ^ m * (4 * 2 ^ δ * k) := by rw [← hY₁]
      _ = 2 ^ (δ + 1) * (Y₁ + 2 * 3 ^ m * k) := by
            rw [pow_succ]
            ring
  exact
    Nat.mul_left_cancel
      (Arithmetic.twoPow_pos (δ + 1)) hMul

/--
`xi = Z/2^δ` の格子差と affine endpoint equation を直接合成した形。

`Z₂ = Z₁ + 2^δ k` なら `Y₂ = Y₁ + 2*3^m*k`。
-/
theorem dyadicState_defectGridShift_implies_affineEndpointShift
    (O : Collatz3.OddOrbit)
    (m t₁ t₂ Y₁ Y₂ k : ℕ)
    (Z₁ Z₂ : ℤ)
    (hXi₁ :
      O.normalizedCompletionDyadicState m t₁ =
        (Z₁ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
    (hXi₂ :
      O.normalizedCompletionDyadicState m t₂ =
        (Z₂ : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)
    (hZ :
      Z₂ = Z₁ +
        (2 : ℤ) ^ infiniteSurvivorDefect O.exponent m * (k : ℤ))
    (hY₁ :
      2 ^ (infiniteSurvivorDefect O.exponent m + 1) * Y₁ =
        O.value m + 3 ^ m * t₁)
    (hY₂ :
      2 ^ (infiniteSurvivorDefect O.exponent m + 1) * Y₂ =
        O.value m + 3 ^ m * t₂) :
    Y₂ = Y₁ + 2 * 3 ^ m * k := by
  have ht :=
    O.dyadicState_defectGridShift_implies_liftShift
      m t₁ t₂ k Z₁ Z₂ hXi₁ hXi₂ hZ
  exact
    O.affineEndpointCandidate_shift_of_liftGridShift
      m (infiniteSurvivorDefect O.exponent m)
      t₁ t₂ Y₁ Y₂ k ht hY₁ hY₂

end OddOrbit

namespace Bridge

/--
endpoint 候補 `Y + 2*3^m*j` の modulo `8` 位相が一致するなら、
branch index は modulo `4` で一致する。

`3^m` は `4` と互いに素なので、endpoint phase は4本の branch residue を識別する。
-/
theorem endpointPhase_mod_eight_implies_branchIndex_mod_four
    (m Y j k : ℕ)
    (hPhase :
      Y + 2 * 3 ^ m * j ≡
        Y + 2 * 3 ^ m * k [MOD 8]) :
    j ≡ k [MOD 4] := by
  have hMul :
      2 * 3 ^ m * j ≡ 2 * 3 ^ m * k [MOD 8] :=
    Nat.ModEq.add_left_cancel' Y hPhase
  have hScaled :
      2 * (3 ^ m * j) ≡
        2 * (3 ^ m * k) [MOD 2 * 4] := by
    simpa [mul_assoc] using hMul
  have hCancelTwo :
      3 ^ m * j ≡ 3 ^ m * k [MOD 4] :=
    Nat.ModEq.mul_left_cancel' (by norm_num : 2 ≠ 0) hScaled
  have hGcd : Nat.gcd 4 (3 ^ m) = 1 := by
    have hGcd' := (Arithmetic.coprime_threePow_twoPow m 2).symm
    norm_num at hGcd'
    exact hGcd'
  exact hCancelTwo.cancel_left_of_coprime hGcd

/--
branch index の差が4未満の範囲では、endpoint modulo `8` 位相は branch を完全に識別する。

これは「4状態」の有限 phase として使うための elimination theorem。
-/
theorem endpointPhase_mod_eight_branchIndex_unique_of_nearby
    (m Y j k : ℕ)
    (hPhase :
      Y + 2 * 3 ^ m * j ≡
        Y + 2 * 3 ^ m * k [MOD 8])
    (hjk : j < k + 4)
    (hkj : k < j + 4) :
    j = k := by
  have hMod :=
    endpointPhase_mod_eight_implies_branchIndex_mod_four
      m Y j k hPhase
  change j % 4 = k % 4 at hMod
  omega

end Bridge
end Collatz3
