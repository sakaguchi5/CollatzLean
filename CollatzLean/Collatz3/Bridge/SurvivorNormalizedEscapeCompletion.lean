import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow
import CollatzLean.Collatz3.Bridge.SurvivorCompletionLift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: normalized escape と critical completion lift の finite exact 接続

actual survivor の幅 `m` で natural completion lift

`C_m = x_0 + 2^D_m t`

が与えられたとする。既存 endpoint bridge は

`2^E_m Y_m = x_m + 3^m t`

である。

これを actual prefix scale `2^D_m / 3^m` で正規化すると

`2^K_m Y_m / 3^m = R_m + 2^D_m t`

が exact に得られる。ここで

* `D_m` は actual prefix depth,
* `E_m` は completion extra depth,
* `K_m = criticalTwoDepth m = D_m + E_m`,
* `R_m` は normalized escape coordinate。

従って completion endpoint の正規化量から巨大な 2進 lift 主項 `2^D_m t` を引くと、
残りは exactly `R_m` である。

新しい completion notion は導入しない。既存 endpoint lift equation と
`SurvivorNormalizedEscape` の座標を有限算術で接続するだけである。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open Filter

/--
completion natural lift の endpoint equation を normalized escape 座標へ移した exact identity。

`2^K_m Y_m / 3^m = R_m + 2^D_m t`。
-/
theorem endpointCompletion_normalized_eq_escape_add_lift
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ((2 : ℝ) ^ Critical.criticalTwoDepth m *
        (O.endpointCompletionEnd SInf hm : ℝ)) /
      (3 : ℝ) ^ m =
    O.normalizedEscapeCoordinate m +
      (2 : ℝ) ^ infinitePrefixDepth O.exponent m * (t : ℝ) := by
  have hEndNat :=
    O.endpointCompletion_endpoint_eq_of_start_lift SInf hm hStart
  have hEnd :
      (2 : ℝ) ^ O.endpointCompletionExtraDepth m *
          (O.endpointCompletionEnd SInf hm : ℝ) =
        (O.value m : ℝ) + (3 : ℝ) ^ m * (t : ℝ) := by
    exact_mod_cast hEndNat
  have hDepth :
      infinitePrefixDepth O.exponent m +
          O.endpointCompletionExtraDepth m =
        Critical.criticalTwoDepth m := by
    have hD := SInf.prefixDepth_le_beatty m
    unfold endpointCompletionExtraDepth Critical.criticalTwoDepth
    omega
  rw [← hDepth]
  unfold normalizedEscapeCoordinate
  calc
    (((2 : ℝ) ^
          (infinitePrefixDepth O.exponent m +
            O.endpointCompletionExtraDepth m)) *
        (O.endpointCompletionEnd SInf hm : ℝ)) /
        (3 : ℝ) ^ m
        =
      ((2 : ℝ) ^ infinitePrefixDepth O.exponent m *
          ((2 : ℝ) ^ O.endpointCompletionExtraDepth m *
            (O.endpointCompletionEnd SInf hm : ℝ))) /
        (3 : ℝ) ^ m := by
          rw [pow_add]
          ring
    _ =
      ((2 : ℝ) ^ infinitePrefixDepth O.exponent m *
          ((O.value m : ℝ) + (3 : ℝ) ^ m * (t : ℝ))) /
        (3 : ℝ) ^ m := by
          rw [hEnd]
    _ =
      ((2 : ℝ) ^ infinitePrefixDepth O.exponent m *
          (O.value m : ℝ)) /
          (3 : ℝ) ^ m +
        (2 : ℝ) ^ infinitePrefixDepth O.exponent m * (t : ℝ) := by
          field_simp

/--
前定理を `R_m` について解いた形。

completion normalized endpoint から `2^D_m t` を引いた残りは actual `R_m` に exact に一致する。
-/
theorem endpointCompletion_normalized_sub_lift_eq_escape
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ((2 : ℝ) ^ Critical.criticalTwoDepth m *
        (O.endpointCompletionEnd SInf hm : ℝ)) /
        (3 : ℝ) ^ m -
      (2 : ℝ) ^ infinitePrefixDepth O.exponent m * (t : ℝ) =
    O.normalizedEscapeCoordinate m := by
  have h :=
    O.endpointCompletion_normalized_eq_escape_add_lift SInf hm hStart
  linarith

/--
`R_m -> L` なら任意の finite natural completion lift について、
completion normalized endpoint から lift 主項を引いた残りは strict に `L` 未満。

これは completion 側の量と real escape limit の接点を有限段階で書いた形。
-/
theorem endpointCompletion_normalized_sub_lift_lt_limit_of_tendsto
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    ((2 : ℝ) ^ Critical.criticalTwoDepth m *
        (O.endpointCompletionEnd SInf hm : ℝ)) /
        (3 : ℝ) ^ m -
      (2 : ℝ) ^ infinitePrefixDepth O.exponent m * (t : ℝ) <
    L := by
  rw [O.endpointCompletion_normalized_sub_lift_eq_escape SInf hm hStart]
  exact O.normalizedEscapeCoordinate_lt_limit_of_tendsto hT m

end OddOrbit
end Collatz3
