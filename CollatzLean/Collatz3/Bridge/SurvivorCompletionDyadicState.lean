import CollatzLean.Collatz3.Bridge.SurvivorCompletionCenteredResidue
import CollatzLean.Collatz3.Bridge.SurvivorCompletionSharpNormalizedBranch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: centered completion 座標と dyadic state

normalized lift `tau` と normalized residue `rho` を midpoint `2` のまわりへ中心化し、

`upsilon = tau - 2`
`sigma   = rho - 2`

とする。さらに

`xi = (upsilon + 3 sigma) / 4`

を一つの実数 state として読む。

`e_m=1` では residue 側と lift 側の branch digit を `h,g` とすると

`3 * 2^s sigma' = sigma + 4h`
`2^(1+s) upsilon' = upsilon + sigma + 4g`

となり、二式を足すことで

`xi' = (xi + g + 2h) / 2^(1+s)`

という dyadic affine map が得られる。

新しい orbit structure は作らず、既存 scalar coordinates の線形結合だけを定義する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- normalized natural lift coefficient を midpoint `2` のまわりへ中心化する。 -/
noncomputable def centeredNormalizedCompletionLiftCoefficient
    (O : Collatz3.OddOrbit)
    (m t : ℕ) : ℝ :=
  O.normalizedCompletionLiftCoefficient m t - 2

/--
centered lift / centered residue をまとめる dyadic state。

`xi = (upsilon + 3 sigma)/4`。
-/
noncomputable def normalizedCompletionDyadicState
    (O : Collatz3.OddOrbit)
    (m t : ℕ) : ℝ :=
  (O.centeredNormalizedCompletionLiftCoefficient m t +
      3 * centeredNormalizedCompletionCocycleResidue
        m (infiniteSurvivorDefect O.exponent m)) / 4

/-- bounded natural lift では centered lift は `(-2,2)` に入る。 -/
theorem centeredNormalizedCompletionLiftCoefficient_mem_Ioo
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (htPos : 0 < t)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1)) :
    -2 < O.centeredNormalizedCompletionLiftCoefficient m t ∧
      O.centeredNormalizedCompletionLiftCoefficient m t < 2 := by
  have hTau :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf htPos ht
  unfold centeredNormalizedCompletionLiftCoefficient
  constructor <;> linarith

/--
固定 `sigma` に対し `xi` は長さ1の open interval に入る。

`(3 sigma - 2)/4 < xi < (3 sigma + 2)/4`。
-/
theorem normalizedCompletionDyadicState_mem_sigma_interval
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (htPos : 0 < t)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1)) :
    let sigma :=
      centeredNormalizedCompletionCocycleResidue
        m (infiniteSurvivorDefect O.exponent m)
    (3 * sigma - 2) / 4 < O.normalizedCompletionDyadicState m t ∧
      O.normalizedCompletionDyadicState m t < (3 * sigma + 2) / 4 := by
  dsimp
  have hU :=
    O.centeredNormalizedCompletionLiftCoefficient_mem_Ioo SInf htPos ht
  unfold normalizedCompletionDyadicState
  constructor <;> nlinarith

/--
branch threshold `tau+rho=4` は centered coordinates では `xi=sigma/2`。
-/
theorem normalizedCompletion_tau_add_rho_eq_four_iff_dyadicState_eq_sigma_half
    (O : Collatz3.OddOrbit)
    (m t : ℕ) :
    O.normalizedCompletionLiftCoefficient m t +
        normalizedCompletionCocycleResidue
          m (infiniteSurvivorDefect O.exponent m) = 4 ↔
      O.normalizedCompletionDyadicState m t =
        centeredNormalizedCompletionCocycleResidue
          m (infiniteSurvivorDefect O.exponent m) / 2 := by
  unfold normalizedCompletionDyadicState
    centeredNormalizedCompletionLiftCoefficient
    centeredNormalizedCompletionCocycleResidue
  constructor <;> intro h <;> nlinarith

/--
centered lift 側は

`2^(1+s) upsilon' = upsilon + sigma + 4g`

という exact digit recurrence を持つ。
-/
theorem exists_centeredNormalizedCompletionLift_transition_digit
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    ∃ g : ℤ,
      (2 : ℝ) ^ (1 + survivorSturmianStep m) *
          O.centeredNormalizedCompletionLiftCoefficient (m + 1) u =
        O.centeredNormalizedCompletionLiftCoefficient m t +
          centeredNormalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) +
          4 * (g : ℝ) := by
  rcases O.exists_normalizedCompletionLiftStep_residue_digit
      SInf hm hStartM hStartN with ⟨j, hj⟩
  have hRec :=
    O.normalizedCompletionLiftStep_eq_sturmianScale_mul_sub SInf m t u
  rcases survivorSturmianStep_eq_zero_or_one m with hs | hs
  · refine ⟨j, ?_⟩
    rw [hs] at hRec ⊢
    norm_num at hRec ⊢
    unfold centeredNormalizedCompletionLiftCoefficient
      centeredNormalizedCompletionCocycleResidue
    rw [hj] at hRec
    linarith
  · refine ⟨j - 1, ?_⟩
    rw [hs] at hRec ⊢
    norm_num at hRec ⊢
    unfold centeredNormalizedCompletionLiftCoefficient
      centeredNormalizedCompletionCocycleResidue
    rw [hj] at hRec
    linarith

/--
future-minimum `e_m=1` 上の dyadic skew-product。

`xi' = (xi + g + 2h) / 2^(1+s)`。
-/
theorem exists_normalizedCompletionDyadicState_transition_digits_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (he : O.exponent m = 1)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u) :
    ∃ g h : ℤ,
      O.normalizedCompletionDyadicState (m + 1) u =
        (O.normalizedCompletionDyadicState m t +
            (g : ℝ) + 2 * (h : ℝ)) /
          (2 : ℝ) ^ (1 + survivorSturmianStep m) := by
  rcases O.exists_centeredNormalizedCompletionLift_transition_digit
      SInf hm hStartM hStartN with ⟨g, hg⟩
  rcases O.exists_centeredNormalizedCompletionCocycleResidue_transition_digit_of_exponent_eq_one
      SInf he with ⟨h, hh⟩
  refine ⟨g, h, ?_⟩
  have hDef := O.infiniteSurvivorDefect_succ_of_exponent_eq_one SInf he
  unfold normalizedCompletionDyadicState
  rw [hDef]
  have hsNonneg : (0 : ℝ) < (2 : ℝ) ^ (1 + survivorSturmianStep m) := by positivity
  apply (eq_div_iff hsNonneg.ne').2
  calc
    (O.centeredNormalizedCompletionLiftCoefficient (m + 1) u +
          3 * centeredNormalizedCompletionCocycleResidue
            (m + 1)
            (infiniteSurvivorDefect O.exponent m + survivorSturmianStep m)) /
          4 *
        (2 : ℝ) ^ (1 + survivorSturmianStep m)
        =
      ((2 : ℝ) ^ (1 + survivorSturmianStep m) *
          O.centeredNormalizedCompletionLiftCoefficient (m + 1) u +
        3 * (2 : ℝ) ^ (1 + survivorSturmianStep m) *
          centeredNormalizedCompletionCocycleResidue
            (m + 1)
            (infiniteSurvivorDefect O.exponent m + survivorSturmianStep m)) / 4 := by
          field_simp
    _ =
      (O.centeredNormalizedCompletionLiftCoefficient m t +
          centeredNormalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) + 4 * (g : ℝ) +
        2 *
          (centeredNormalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) + 4 * (h : ℝ))) / 4 := by
          rw [hg]
          have hh' := hh
          rw [hDef] at hh'
          have :
              3 * (2 : ℝ) ^ (1 + survivorSturmianStep m) *
                  centeredNormalizedCompletionCocycleResidue
                    (m + 1)
                    (infiniteSurvivorDefect O.exponent m + survivorSturmianStep m) =
                2 *
                  (centeredNormalizedCompletionCocycleResidue
                    m (infiniteSurvivorDefect O.exponent m) + 4 * (h : ℝ)) := by
            rw [show 1 + survivorSturmianStep m =
                survivorSturmianStep m + 1 by omega, pow_succ]
            nlinarith [hh']
          rw [this]
    _ =
      O.normalizedCompletionDyadicState m t + (g : ℝ) + 2 * (h : ℝ) := by
          unfold normalizedCompletionDyadicState
          ring

end OddOrbit
end Collatz3
