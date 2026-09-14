import CollatzLean.Collatz3.Bridge.SurvivorCompletionLift
import CollatzLean.Collatz3.Arithmetic.Signed

/-!
# Collatz3 Bridge: critical completion lift の隣接 cocycle

`SurvivorCompletionLift` では、十分先の各幅 `m` に対して

`C_m = x + 2^D_m * t_m`

という一意な正奇数 lift が得られた。

このファイルでは隣接幅 `m -> m+1` を比較する。
新しい primitive data は導入せず、Beatty roof の一歩差、survivor defect、
completion extra depth、既存 lift からすべてを derived theorem として導く。

中心式は、符号付き lift 差

`q_m = 2^(e_m) * t_(m+1) - t_m`

に対する

`3^(m+1) q_m + 1
   = 2^E_m (2^b_m Y_(m+1) - 3 Y_m)`

である。ここで

* `E_m = δ_m + 1`,
* `b_m = 1 + survivorSturmianStep m ∈ {1,2}`。

右辺括弧は必ず奇数なので、左辺の 2進 divisibility depth は exactly `E_m`。
-/

namespace Collatz3
namespace Bridge

/--
critical terminal depth の一歩増分。

Beatty index は一歩で `1` または `2` 増えるため、
この値も exact に `1` または `2`。
-/
def completionCriticalStep (m : ℕ) : ℕ :=
  1 + survivorSturmianStep m

/-- critical terminal depth の一歩増分は `1` または `2`。 -/
theorem completionCriticalStep_eq_one_or_two (m : ℕ) :
    completionCriticalStep m = 1 ∨ completionCriticalStep m = 2 := by
  rcases survivorSturmianStep_eq_zero_or_one m with h | h
  · left
    simp [completionCriticalStep, h]
  · right
    simp [completionCriticalStep, h]

/-- critical terminal depth の一歩増分は正。 -/
theorem completionCriticalStep_pos (m : ℕ) :
    0 < completionCriticalStep m := by
  rcases completionCriticalStep_eq_one_or_two m with h | h <;> omega

/--
critical terminal depth の exact 一歩更新。

`K_(m+1) = K_m + b_m`。
-/
theorem criticalTwoDepth_succ_eq_add_completionCriticalStep
    (m : ℕ) :
    Critical.criticalTwoDepth (m + 1) =
      Critical.criticalTwoDepth m + completionCriticalStep m := by
  have hLo := Critical.beattyIndex_lt_succ m
  have hHi := beattyIndex_succ_le_add_two m
  have hm := index_le_beattyIndex m
  have hm1 := index_le_beattyIndex (m + 1)
  unfold completionCriticalStep survivorSturmianStep survivorRoofExcess
    Critical.criticalTwoDepth
  omega

/-- `n % 2 = 1` を通常の `Odd n` witness に戻す小さい補題。 -/
theorem odd_of_mod_two_eq_one
    {n : ℕ}
    (h : n % 2 = 1) :
    Odd n := by
  refine ⟨n / 2, ?_⟩
  omega

end Bridge

namespace OddOrbit

open Bridge

/--
actual exponent、completion extra depth、critical terminal step の exact balance。

`D_(m+1)=D_m+e_m` と `K_(m+1)=K_m+b_m` から

`e_m + E_(m+1) = E_m + b_m`

を得る。
-/
theorem endpointCompletionExtraDepth_balance
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.exponent m + O.endpointCompletionExtraDepth (m + 1) =
      O.endpointCompletionExtraDepth m + completionCriticalStep m := by
  have hDm :
      infinitePrefixDepth O.exponent m ≤ Critical.criticalTwoDepth m := by
    have h := SInf.prefixDepth_le_beatty m
    unfold Critical.criticalTwoDepth
    omega
  have hDn :
      infinitePrefixDepth O.exponent (m + 1) ≤
        Critical.criticalTwoDepth (m + 1) := by
    have h := SInf.prefixDepth_le_beatty (m + 1)
    unfold Critical.criticalTwoDepth
    omega
  have hK := criticalTwoDepth_succ_eq_add_completionCriticalStep m
  rw [infinitePrefixDepth_succ, hK] at hDn
  unfold endpointCompletionExtraDepth
  rw [infinitePrefixDepth_succ, hK]
  omega

/--
`e_m = 1` なら extra depth は Sturmian roof step だけ増える。

`E_(m+1) = E_m + s_m`。
-/
theorem endpointCompletionExtraDepth_succ_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (he : O.exponent m = 1) :
    O.endpointCompletionExtraDepth (m + 1) =
      O.endpointCompletionExtraDepth m + survivorSturmianStep m := by
  have h := O.endpointCompletionExtraDepth_balance SInf m
  unfold completionCriticalStep at h
  rw [he] at h
  omega

/--
`e_m = 1` なら extra depth は据え置きか `+1` のどちらか。 -/
theorem endpointCompletionExtraDepth_succ_eq_self_or_succ_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (he : O.exponent m = 1) :
    O.endpointCompletionExtraDepth (m + 1) = O.endpointCompletionExtraDepth m ∨
      O.endpointCompletionExtraDepth (m + 1) = O.endpointCompletionExtraDepth m + 1 := by
  have h := O.endpointCompletionExtraDepth_succ_of_exponent_eq_one SInf he
  rcases survivorSturmianStep_eq_zero_or_one m with hs | hs
  · left
    rw [hs] at h
    simpa using h
  · right
    rw [hs] at h
    simpa using h

/--
`e_m = 1` なら survivor defect も Sturmian roof step だけ増える。

`δ_(m+1) = δ_m + s_m`。
-/
theorem infiniteSurvivorDefect_succ_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (he : O.exponent m = 1) :
    infiniteSurvivorDefect O.exponent (m + 1) =
      infiniteSurvivorDefect O.exponent m + survivorSturmianStep m := by
  have h := infiniteSurvivorDefect_succ SInf m
  rw [he] at h
  simpa using h

/--
`e_m = 1` の位置では defect は据え置きか `+1`。特に減少しない。
-/
theorem infiniteSurvivorDefect_succ_eq_self_or_succ_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (he : O.exponent m = 1) :
    infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m ∨
      infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m + 1 := by
  have h := O.infiniteSurvivorDefect_succ_of_exponent_eq_one SInf he
  rcases survivorSturmianStep_eq_zero_or_one m with hs | hs
  · left
    rw [hs] at h
    simpa using h
  · right
    rw [hs] at h
    simpa using h

/--
roof return `δ_m=0` の直後の exponent は `1` または `2` に限られる。
-/
theorem exponent_eq_one_or_two_of_defect_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hZero : infiniteSurvivorDefect O.exponent m = 0) :
    O.exponent m = 1 ∨ O.exponent m = 2 := by
  have hExp := exponent_eq_one_add_step_add_defect_sub SInf m
  have hStep := survivorSturmianStep_le_one m
  have hPos := SInf.exponent_pos m
  rw [hZero] at hExp
  omega

/--
roof return の一歩後に起こり得る defect transition の完全な三分岐。

* `e=1, s=0` なら defect は `0` のまま。
* `e=1, s=1` なら defect は `1` へ出る。
* `e=2` なら必ず `s=1` で defect は `0` のまま。
-/
theorem defect_zero_transition_cases
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hZero : infiniteSurvivorDefect O.exponent m = 0) :
    (O.exponent m = 1 ∧ survivorSturmianStep m = 0 ∧
        infiniteSurvivorDefect O.exponent (m + 1) = 0) ∨
    (O.exponent m = 1 ∧ survivorSturmianStep m = 1 ∧
        infiniteSurvivorDefect O.exponent (m + 1) = 1) ∨
    (O.exponent m = 2 ∧ survivorSturmianStep m = 1 ∧
        infiniteSurvivorDefect O.exponent (m + 1) = 0) := by
  have hRec := infiniteSurvivorDefect_succ SInf m
  have hExpCases := O.exponent_eq_one_or_two_of_defect_zero SInf hZero
  have hExpEq := exponent_eq_one_add_step_add_defect_sub SInf m
  have hStep := survivorSturmianStep_eq_zero_or_one m
  rcases hExpCases with he | he <;> rcases hStep with hs | hs
  · left
    rw [hZero, he, hs] at hRec
    simpa [he, hs] using hRec
  · right; left
    rw [hZero, he, hs] at hRec
    simpa [he, hs] using hRec
  · rw [hZero, he, hs] at hExpEq
    omega
  · right; right
    rw [hZero, he, hs] at hRec
    simpa [he, hs] using hRec

/--
隣接 natural lift の符号付き差。

Nat subtraction ではなく整数差として

`q_m = 2^(e_m) * t_(m+1) - t_m`

を保存する。
-/
def endpointCompletionLiftStep
    (O : Collatz3.OddOrbit)
    (m t u : ℕ) : ℤ :=
  ((2 ^ O.exponent m * u : ℕ) : ℤ) - (t : ℤ)

/-- `e_m=1` では lift step は `2u-t`。 -/
theorem endpointCompletionLiftStep_eq_two_mul_sub_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (he : O.exponent m = 1) :
    endpointCompletionLiftStep O m t u =
      2 * (u : ℤ) - (t : ℤ) := by
  unfold endpointCompletionLiftStep
  rw [he]
  norm_num

/--
`t_m` が奇数なら signed lift step も奇数。

`e_m>0` なので `2^(e_m)u` は偶数であり、偶数から奇数を引いた差は奇数。
-/
theorem endpointCompletionLiftStep_odd
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (hePos : 0 < O.exponent m)
    (htOdd : Odd t) :
    Odd (endpointCompletionLiftStep O m t u) := by
  rcases htOdd with ⟨a, ha⟩
  obtain ⟨d, hd⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hePos)
  refine ⟨(((2 ^ d * u : ℕ) : ℤ) - (a : ℤ) - 1), ?_⟩
  unfold endpointCompletionLiftStep
  rw [hd, ha, pow_succ]
  push_cast
  ring

/-- 奇数 lift step は `0` ではない。 -/
theorem endpointCompletionLiftStep_ne_zero
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (hePos : 0 < O.exponent m)
    (htOdd : Odd t) :
    endpointCompletionLiftStep O m t u ≠ 0 := by
  have hOdd := O.endpointCompletionLiftStep_odd (u := u) hePos htOdd
  intro hZero
  rw [hZero] at hOdd
  rcases hOdd with ⟨z, hz⟩
  omega

/--
隣接 completion starts の整数差は、actual depth `D_m` を exact に因子として持つ。

`C_(m+1)-C_m = 2^D_m q_m`。
-/
theorem endpointCompletionStart_sub_eq_twoPow_mul_liftStep
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
    (O.endpointCompletionStart SInf (by omega : 0 < m + 1) : ℤ) -
        (O.endpointCompletionStart SInf hm : ℤ) =
      (2 : ℤ) ^ infinitePrefixDepth O.exponent m *
        endpointCompletionLiftStep O m t u := by
  rw [hStartM, hStartN]
  unfold endpointCompletionLiftStep
  rw [infinitePrefixDepth_succ, pow_add]
  push_cast
  ring

/--
隣接 endpoint lift cocycle の奇数 cofactor。

`b_m ∈ {1,2}` かつ両 canonical endpoint が奇数なので

`2^b_m Y_(m+1) - 3 Y_m`

は必ず奇数。
-/
theorem endpointCompletionCocycleFactor_odd
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Odd
      ((2 : ℤ) ^ completionCriticalStep m *
          (O.endpointCompletionEnd SInf (by omega : 0 < m + 1) : ℤ) -
        3 * (O.endpointCompletionEnd SInf hm : ℤ)) := by
  rcases O.endpointCompletionEnd_odd SInf hm with ⟨a, ha⟩
  rcases O.endpointCompletionEnd_odd SInf (by omega : 0 < m + 1) with ⟨b, hb⟩
  rcases completionCriticalStep_eq_one_or_two m with hs | hs
  · refine ⟨2 * (b : ℤ) - 3 * (a : ℤ) - 1, ?_⟩
    rw [hs, ha, hb]
    push_cast
    ring
  · refine ⟨4 * (b : ℤ) - 3 * (a : ℤ), ?_⟩
    rw [hs, ha, hb]
    push_cast
    ring

/--
隣接 natural lifts の exact endpoint cocycle。

`q_m = 2^(e_m)t_(m+1)-t_m` とすると

`3^(m+1) q_m + 1
 = 2^E_m (2^b_m Y_(m+1)-3Y_m)`。
-/
theorem endpointCompletion_endpoint_cocycle
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
    (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1 =
      (2 : ℤ) ^ O.endpointCompletionExtraDepth m *
        ((2 : ℤ) ^ completionCriticalStep m *
            (O.endpointCompletionEnd SInf (by omega : 0 < m + 1) : ℤ) -
          3 * (O.endpointCompletionEnd SInf hm : ℤ)) := by
  let e := O.exponent m
  let E := O.endpointCompletionExtraDepth m
  let EN := O.endpointCompletionExtraDepth (m + 1)
  let b := completionCriticalStep m
  let y := O.value m
  let yN := O.value (m + 1)
  let Y := O.endpointCompletionEnd SInf hm
  let YN := O.endpointCompletionEnd SInf (by omega : 0 < m + 1)
  have hMNat :=
    O.endpointCompletion_endpoint_eq_of_start_lift SInf hm hStartM
  have hNNat :=
    O.endpointCompletion_endpoint_eq_of_start_lift SInf
      (by omega : 0 < m + 1) hStartN
  have hM :
      (2 : ℤ) ^ E * (Y : ℤ) =
        (y : ℤ) + (3 : ℤ) ^ m * (t : ℤ) := by
    exact_mod_cast hMNat
  have hN :
      (2 : ℤ) ^ EN * (YN : ℤ) =
        (yN : ℤ) + (3 : ℤ) ^ (m + 1) * (u : ℤ) := by
    exact_mod_cast hNNat
  have hStepNat := (O.step m).equation
  have hStep :
      (2 : ℤ) ^ e * (yN : ℤ) = 3 * (y : ℤ) + 1 := by
    exact_mod_cast hStepNat
  have hBalance : e + EN = E + b := by
    simpa [e, E, EN, b] using O.endpointCompletionExtraDepth_balance SInf m
  have hStep' :
      (2 : ℤ) ^ O.exponent m * (yN : ℤ) =
        3 * (y : ℤ) + 1 := by
    simpa [e] using hStep
  calc
    (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1
        =
        (2 : ℤ) ^ e *
            ((yN : ℤ) + (3 : ℤ) ^ (m + 1) * (u : ℤ)) -
          3 * ((y : ℤ) + (3 : ℤ) ^ m * (t : ℤ)) := by
            unfold endpointCompletionLiftStep
            push_cast
            dsimp [e]
            rw [mul_add, hStep', pow_succ]
            ring
    _ =
        (2 : ℤ) ^ e * ((2 : ℤ) ^ EN * (YN : ℤ)) -
          3 * ((2 : ℤ) ^ E * (Y : ℤ)) := by
            rw [← hN, ← hM]
    _ =
        (2 : ℤ) ^ (e + EN) * (YN : ℤ) -
          3 * ((2 : ℤ) ^ E * (Y : ℤ)) := by
            rw [pow_add]
            ring
    _ =
        (2 : ℤ) ^ (E + b) * (YN : ℤ) -
          3 * ((2 : ℤ) ^ E * (Y : ℤ)) := by
            rw [hBalance]
    _ =
        (2 : ℤ) ^ E *
          ((2 : ℤ) ^ b * (YN : ℤ) - 3 * (Y : ℤ)) := by
            rw [pow_add]
            ring
    _ =
      (2 : ℤ) ^ O.endpointCompletionExtraDepth m *
        ((2 : ℤ) ^ completionCriticalStep m *
            (O.endpointCompletionEnd SInf (by omega : 0 < m + 1) : ℤ) -
          3 * (O.endpointCompletionEnd SInf hm : ℤ)) := by
            rfl

/--
隣接 cocycle の 2進 divisibility depth は exactly `E_m`。

`v₂` を新しい primitive として導入せず、

* `2^E_m` は割り切る、
* `2^(E_m+1)` は割り切らない

の二本で保存する。
-/
theorem endpointCompletion_endpoint_cocycle_exact_twoDepth
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
    ((2 : ℤ) ^ O.endpointCompletionExtraDepth m ∣
      (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1) ∧
    ¬ ((2 : ℤ) ^ (O.endpointCompletionExtraDepth m + 1) ∣
      (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1) := by
  let E := O.endpointCompletionExtraDepth m
  let F : ℤ :=
    (2 : ℤ) ^ completionCriticalStep m *
        (O.endpointCompletionEnd SInf (by omega : 0 < m + 1) : ℤ) -
      3 * (O.endpointCompletionEnd SInf hm : ℤ)
  let A : ℤ :=
    (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1
  have hEq : A = (2 : ℤ) ^ E * F := by
    simpa [A, E, F] using
      O.endpointCompletion_endpoint_cocycle SInf hm hStartM hStartN
  have hOdd : Odd F := by
    simpa [F] using O.endpointCompletionCocycleFactor_odd SInf hm
  constructor
  · refine ⟨F, ?_⟩
    exact hEq
  · intro hDiv
    rcases hDiv with ⟨k, hk⟩
    have hMul :
        (2 : ℤ) ^ E * F =
          (2 : ℤ) ^ E * (2 * k) := by
      calc
        (2 : ℤ) ^ E * F = A := hEq.symm
        _ = (2 : ℤ) ^ (E + 1) * k := hk
        _ = (2 : ℤ) ^ E * (2 * k) := by
              rw [pow_succ]
              ring
    have hPowNe : (2 : ℤ) ^ E ≠ 0 := by
      exact pow_ne_zero E (by norm_num)
    have hFEven : F = 2 * k :=
      mul_left_cancel₀ hPowNe hMul
    rcases hOdd with ⟨z, hz⟩
    rw [hFEven] at hz
    omega

/--
隣接 cocycle の exact 2進 depth を survivor defect で書いた形。

`E_m = δ_m+1` を代入して

* `2^(δ_m+1)` は割り切る、
* `2^(δ_m+2)` は割り切らない

を得る。
-/
theorem endpointCompletion_endpoint_cocycle_exact_defectDepth
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
    ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent m + 1) ∣
      (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1) ∧
    ¬ ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent m + 2) ∣
      (3 : ℤ) ^ (m + 1) * endpointCompletionLiftStep O m t u + 1) := by
  have h :=
    O.endpointCompletion_endpoint_cocycle_exact_twoDepth
      SInf hm hStartM hStartN
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
  simpa [Nat.add_assoc] using h

/--
`e_m=1` の位置における signed lift step の粗い一様区間。

`E_(m+1) ∈ {E_m,E_m+1}` と両 lift の canonical modulus 上界だけから

`-2^(E_m+1) < q_m < 2^(E_m+3)`

を得る。深い modulus に対して integer branch が定数幅にしか広がらないことを表す。
-/
theorem endpointCompletionLiftStep_bounds_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (he : O.exponent m = 1)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    -((2 : ℤ) ^ (O.endpointCompletionExtraDepth m + 1)) <
        endpointCompletionLiftStep O m t u ∧
      endpointCompletionLiftStep O m t u <
        (2 : ℤ) ^ (O.endpointCompletionExtraDepth m + 3) := by
  let E := O.endpointCompletionExtraDepth m
  let EN := O.endpointCompletionExtraDepth (m + 1)
  have hEcases :=
    O.endpointCompletionExtraDepth_succ_eq_self_or_succ_of_exponent_eq_one SInf he
  have hENle : EN ≤ E + 1 := by
    dsimp [E, EN]
    rcases hEcases with hEq | hEq <;> omega
  have hPowLe : 2 ^ (EN + 1) ≤ 2 ^ (E + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
  have hu' : u < 2 ^ (EN + 1) := by
    simpa [EN] using hu
  have huUniform : u < 2 ^ (E + 2) :=
    lt_of_lt_of_le hu' hPowLe
  have ht' : t < 2 ^ (E + 1) := by
    simpa [E] using ht
  have htZ : (t : ℤ) < (2 : ℤ) ^ (E + 1) := by
    exact_mod_cast ht'
  have huUniformZ : (u : ℤ) < (2 : ℤ) ^ (E + 2) := by
    exact_mod_cast huUniform
  have huNonneg : (0 : ℤ) ≤ (u : ℤ) := by omega
  have htNonneg : (0 : ℤ) ≤ (t : ℤ) := by omega
  have hDouble :
      2 * (u : ℤ) < (2 : ℤ) ^ (E + 3) := by
    have hPow :
        (2 : ℤ) ^ (E + 3) = 2 * (2 : ℤ) ^ (E + 2) := by
      rw [show E + 3 = E + 2 + 1 by omega, pow_succ]
      ring
    rw [hPow]
    nlinarith
  rw [O.endpointCompletionLiftStep_eq_two_mul_sub_of_exponent_eq_one he]
  constructor <;> nlinarith


/--
`e_m=1` の lift-step 区間を defect 座標で書いた形。

`E_m=δ_m+1` なので

`-2^(δ_m+2) < q_m < 2^(δ_m+4)`。
-/
theorem endpointCompletionLiftStep_bounds_defect_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (he : O.exponent m = 1)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    -((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent m + 2)) <
        endpointCompletionLiftStep O m t u ∧
      endpointCompletionLiftStep O m t u <
        (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent m + 4) := by
  have h := O.endpointCompletionLiftStep_bounds_of_exponent_eq_one
    SInf he ht hu
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
  simpa [Nat.add_assoc] using h

end OddOrbit
end Collatz3
