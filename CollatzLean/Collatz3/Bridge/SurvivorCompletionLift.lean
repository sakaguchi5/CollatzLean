import CollatzLean.Collatz3.Bridge.SurvivorCompletionArithmetic
import Mathlib.Data.Nat.ModEq

/-!
# Collatz3 Bridge: actual survivor start と critical completion start の exact 2進 lift

`SurvivorCompletionArithmetic` で、actual prefix と critical completion が同じ affine
translation `B_m` を持つことを得た。

ここでは

`D_m = infinitePrefixDepth O.exponent m`

と置き、completion canonical start `C_m` と actual start `x = O.value 0` を比較する。
中心結果は

* `C_m = x (mod 2^D_m)`,
* `C_m = x + 2^D_m (mod 2^(D_m+1))`,

である。従って最初に異なる 2進 bit は exact に `D_m`。

さらに `x < 2^D_m` となった後は自然数 lift

`C_m = x + 2^D_m * t_m`

が一意に存在し、`t_m` は正の奇数で、completion endpoint `Y_m` と actual endpoint `y_m`
の間に

`2^(δ_m+1) * Y_m = y_m + 3^m * t_m`

という exact Hensel 型 bridge を与える。
-/

namespace Collatz3
namespace Bridge

/-- `3^m` は自然数として常に奇数。 -/
theorem threePow_odd_nat (m : ℕ) : Odd (3 ^ m) := by
  induction m with
  | zero =>
      exact ⟨0, by simp⟩
  | succ m ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨3 * q + 1, ?_⟩
      rw [pow_succ, hq]
      ring

end Bridge

namespace OddOrbit

open Bridge

/-- infinite survivor の prefix depth は index に対して strict monotone。 -/
theorem infinitePrefixDepth_lt_of_lt
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {r s : ℕ}
    (hrs : r < s) :
    infinitePrefixDepth O.exponent r <
      infinitePrefixDepth O.exponent s := by
  induction s generalizing r with
  | zero =>
      omega
  | succ s ih =>
      by_cases hrsEq : r = s
      · subst r
        rw [infinitePrefixDepth_succ]
        have he := SInf.exponent_pos s
        omega
      · have hrs' : r < s := by omega
        have hIH := ih hrs'
        rw [infinitePrefixDepth_succ]
        have he := SInf.exponent_pos s
        omega

/--
completion canonical start と actual start は depth `D_m` まで同じ 2進 residue を持つ。
-/
theorem endpointCompletionStart_modEq_start
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    O.endpointCompletionStart SInf hm ≡ O.value 0
      [MOD 2 ^ infinitePrefixDepth O.exponent m] := by
  let D := infinitePrefixDepth O.exponent m
  let K := Critical.criticalTwoDepth m
  let B := Word.affineConst (O.segmentWord 0 m)
  let C := O.endpointCompletionStart SInf hm
  let Y := O.endpointCompletionEnd SInf hm
  let x := O.value 0
  let y := O.value m
  have hActual : 2 ^ D * y = 3 ^ m * x + B := by
    simpa [D, y, x, B] using O.endpointSegment_req_equation m
  have hComp : 2 ^ K * Y = 3 ^ m * C + B := by
    simpa [K, Y, C, B] using O.endpointCompletion_req_equation SInf hm
  have hDK : D ≤ K := by
    have hRoof := SInf.prefixDepth_le_beatty m
    dsimp [D, K]
    omega
  have hPowDvd : 2 ^ D ∣ 2 ^ K :=
    Nat.pow_dvd_pow 2 hDK
  have hCompDvd : 2 ^ D ∣ 3 ^ m * C + B := by
    rw [← hComp]
    rcases hPowDvd with ⟨q, hq⟩
    refine ⟨q * Y, ?_⟩
    rw [hq]
    ring
  have hActualDvd : 2 ^ D ∣ 3 ^ m * x + B := by
    rw [← hActual]
    exact Nat.dvd_mul_right _ _
  have hSum :
      3 ^ m * C + B ≡ 3 ^ m * x + B [MOD 2 ^ D] :=
    hCompDvd.modEq_zero_nat.trans hActualDvd.modEq_zero_nat.symm
  have hB : B ≡ B [MOD 2 ^ D] := Nat.ModEq.rfl
  have hMul : 3 ^ m * C ≡ 3 ^ m * x [MOD 2 ^ D] :=
    hB.add_right_cancel hSum
  have hGcd : Nat.gcd (2 ^ D) (3 ^ m) = 1 := by
    exact (Arithmetic.coprime_threePow_twoPow m D).symm
  have hCX : C ≡ x [MOD 2 ^ D] :=
    hMul.cancel_left_of_coprime hGcd
  simpa [C, x, D] using hCX

/--
次の 1 bit では completion と actual start が必ず反対側へ分かれる。

`C_m` は `x + 2^D_m` と同じ residue modulo `2^(D_m+1)` を持つ。
これが「最初の相違 bit = D_m」の stronger half。
-/
theorem endpointCompletionStart_modEq_start_add_twoPow
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    O.endpointCompletionStart SInf hm ≡
      O.value 0 + 2 ^ infinitePrefixDepth O.exponent m
      [MOD 2 ^ (infinitePrefixDepth O.exponent m + 1)] := by
  let D := infinitePrefixDepth O.exponent m
  let K := Critical.criticalTwoDepth m
  let B := Word.affineConst (O.segmentWord 0 m)
  let C := O.endpointCompletionStart SInf hm
  let Y := O.endpointCompletionEnd SInf hm
  let x := O.value 0
  let y := O.value m
  have hActual : 2 ^ D * y = 3 ^ m * x + B := by
    simpa [D, y, x, B] using O.endpointSegment_req_equation m
  have hComp : 2 ^ K * Y = 3 ^ m * C + B := by
    simpa [K, Y, C, B] using O.endpointCompletion_req_equation SInf hm
  have hDK : D + 1 ≤ K := by
    have hRoof := SInf.prefixDepth_le_beatty m
    dsimp [D, K]
    omega
  have hPowDvd : 2 ^ (D + 1) ∣ 2 ^ K :=
    Nat.pow_dvd_pow 2 hDK
  have hCompDvd : 2 ^ (D + 1) ∣ 3 ^ m * C + B := by
    rw [← hComp]
    rcases hPowDvd with ⟨q, hq⟩
    refine ⟨q * Y, ?_⟩
    rw [hq]
    ring
  have hTargetDvd :
      2 ^ (D + 1) ∣ 3 ^ m * (x + 2 ^ D) + B := by
    rcases O.value_odd m with ⟨u, hu⟩
    rcases threePow_odd_nat m with ⟨v, hv⟩
    have huy : y = 2 * u + 1 := by
      simpa [y] using hu
    refine ⟨u + v + 1, ?_⟩
    calc
      3 ^ m * (x + 2 ^ D) + B
          = (3 ^ m * x + B) + 3 ^ m * 2 ^ D := by
              ring
      _ = 2 ^ D * y + 3 ^ m * 2 ^ D := by
              rw [← hActual]
      _ = 2 ^ D * ((2 * u + 1) + (2 * v + 1)) := by
              rw [huy, hv]
              ring
      _ = 2 ^ (D + 1) * (u + v + 1) := by
            rw [pow_succ]
            ring
  have hSum :
      3 ^ m * C + B ≡
        3 ^ m * (x + 2 ^ D) + B
        [MOD 2 ^ (D + 1)] :=
    hCompDvd.modEq_zero_nat.trans hTargetDvd.modEq_zero_nat.symm
  have hB : B ≡ B [MOD 2 ^ (D + 1)] := Nat.ModEq.rfl
  have hMul :
      3 ^ m * C ≡ 3 ^ m * (x + 2 ^ D)
        [MOD 2 ^ (D + 1)] :=
    hB.add_right_cancel hSum
  have hGcd : Nat.gcd (2 ^ (D + 1)) (3 ^ m) = 1 := by
    exact (Arithmetic.coprime_threePow_twoPow m (D + 1)).symm
  have hCX : C ≡ x + 2 ^ D [MOD 2 ^ (D + 1)] :=
    hMul.cancel_left_of_coprime hGcd
  simpa [C, x, D] using hCX

/--
completion start と actual start は modulo `2^(D_m+1)` では一致しない。
従って一致深度は exactly `D_m`。
-/
theorem endpointCompletionStart_not_modEq_start_succ
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    ¬ O.endpointCompletionStart SInf hm ≡ O.value 0
      [MOD 2 ^ (infinitePrefixDepth O.exponent m + 1)] := by
  let D := infinitePrefixDepth O.exponent m
  let C := O.endpointCompletionStart SInf hm
  let x := O.value 0
  have hShift := O.endpointCompletionStart_modEq_start_add_twoPow SInf hm
  intro hSame
  have hBad : x ≡ x + 2 ^ D [MOD 2 ^ (D + 1)] := by
    have h1 : x ≡ C [MOD 2 ^ (D + 1)] := by
      simpa [C, x, D] using hSame.symm
    have h2 : C ≡ x + 2 ^ D [MOD 2 ^ (D + 1)] := by
      simpa [C, x, D] using hShift
    exact h1.trans h2
  have hDiv : 2 ^ (D + 1) ∣ 2 ^ D := by
    have hLe : x ≤ x + 2 ^ D := by simp
    simpa using (Nat.modEq_iff_dvd' hLe).mp hBad
  have hLePow : 2 ^ (D + 1) ≤ 2 ^ D :=
    Nat.le_of_dvd (Arithmetic.twoPow_pos D) hDiv
  rw [pow_succ] at hLePow
  have hPos := Arithmetic.twoPow_pos D
  omega

/--
一つの completion start についての exact 2進 depth package。
低い `D_m` bit までは actual start と一致し、次の bit では必ず異なる。
-/
theorem endpointCompletionStart_exact_twoDepth
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    (O.endpointCompletionStart SInf hm ≡ O.value 0
      [MOD 2 ^ infinitePrefixDepth O.exponent m]) ∧
    ¬ (O.endpointCompletionStart SInf hm ≡ O.value 0
      [MOD 2 ^ (infinitePrefixDepth O.exponent m + 1)]) := by
  exact
    ⟨O.endpointCompletionStart_modEq_start SInf hm,
      O.endpointCompletionStart_not_modEq_start_succ SInf hm⟩

/--
自然数 lift の start equation から completion endpoint equation を exact に回収する。

`E_m = criticalTwoDepth m - D_m` とすると

`C_m = x + 2^D_m t`

なら

`2^E_m Y_m = y_m + 3^m t`。
-/
theorem endpointCompletion_endpoint_eq_of_start_lift
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hStart :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t) :
    2 ^ O.endpointCompletionExtraDepth m *
        O.endpointCompletionEnd SInf hm =
      O.value m + 3 ^ m * t := by
  let D := infinitePrefixDepth O.exponent m
  let K := Critical.criticalTwoDepth m
  let E := O.endpointCompletionExtraDepth m
  let B := Word.affineConst (O.segmentWord 0 m)
  let C := O.endpointCompletionStart SInf hm
  let Y := O.endpointCompletionEnd SInf hm
  let x := O.value 0
  let y := O.value m
  have hActual : 2 ^ D * y = 3 ^ m * x + B := by
    simpa [D, y, x, B] using O.endpointSegment_req_equation m
  have hComp : 2 ^ K * Y = 3 ^ m * C + B := by
    simpa [K, Y, C, B] using O.endpointCompletion_req_equation SInf hm
  have hDK : D ≤ K := by
    have hRoof := SInf.prefixDepth_le_beatty m
    dsimp [D, K]
    omega
  have hK : D + E = K := by
    dsimp [D, E, K, endpointCompletionExtraDepth]
    exact Nat.add_sub_of_le hDK
  have hStart' : C = x + 2 ^ D * t := by
    simpa [C, x, D] using hStart
  have hMul :
      2 ^ D * (2 ^ E * Y) =
        2 ^ D * (y + 3 ^ m * t) := by
    calc
      2 ^ D * (2 ^ E * Y)
          = (2 ^ D * 2 ^ E) * Y := by
              ring
      _ = 2 ^ (D + E) * Y := by
              rw [pow_add]
      _ = 2 ^ K * Y := by
              rw [hK]
      _ = 3 ^ m * C + B := hComp
      _ = 3 ^ m * (x + 2 ^ D * t) + B := by rw [hStart']
      _ = (3 ^ m * x + B) + 2 ^ D * (3 ^ m * t) := by ring
      _ = 2 ^ D * y + 2 ^ D * (3 ^ m * t) := by
              rw [← hActual]
      _ = 2 ^ D * (y + 3 ^ m * t) := by ring
  have hCancel :=
    Nat.mul_left_cancel (Arithmetic.twoPow_pos D) hMul
  simpa [E, Y, y] using hCancel

/--
`x < 2^D_m` となった後は completion start の lift coefficient `t_m` が自然数として存在する。
さらに `t_m` は正の奇数、full completion modulus から得る上界を持ち、endpoint bridge も満たす。
-/
theorem exists_endpointCompletionNatLift
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m)
    (hx : O.value 0 < 2 ^ infinitePrefixDepth O.exponent m) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t ∧
      0 < t ∧
      t % 2 = 1 ∧
      t < 2 ^ (O.endpointCompletionExtraDepth m + 1) ∧
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf hm =
        O.value m + 3 ^ m * t := by
  let D := infinitePrefixDepth O.exponent m
  let K := Critical.criticalTwoDepth m
  let E := O.endpointCompletionExtraDepth m
  let C := O.endpointCompletionStart SInf hm
  let x := O.value 0
  have hLow := O.endpointCompletionStart_modEq_start SInf hm
  have hHigh := O.endpointCompletionStart_modEq_start_add_twoPow SInf hm
  have hx' : x < 2 ^ D := by
    simpa [x, D] using hx
  have hTargetLt : x + 2 ^ D < C + 2 ^ (D + 1) := by
    rw [pow_succ]
    omega
  have hTargetLe : x + 2 ^ D ≤ C := by
    have h := hHigh.symm.le_of_lt_add hTargetLt
    simpa [C, x, D] using h
  have hxC : x ≤ C := by omega
  have hLow' : x ≡ C [MOD 2 ^ D] := by
    simpa [C, x, D] using hLow.symm
  rcases (Nat.modEq_iff_exists_eq_add hxC).1 hLow' with ⟨t, hStart⟩
  have hStart' : C = x + 2 ^ D * t := hStart
  have hHigh' :
      x + 2 ^ D * t ≡ x + 2 ^ D [MOD 2 ^ (D + 1)] := by
    rw [← hStart']
    simpa [C, x, D] using hHigh
  have hScaled :
      2 ^ D * t ≡ 2 ^ D [MOD 2 ^ (D + 1)] :=
    Nat.ModEq.add_left_cancel' x hHigh'
  have hScaled' :
      2 ^ D * t ≡ 2 ^ D * 1 [MOD 2 ^ D * 2] := by
    simpa [pow_succ] using hScaled
  have htModEq : t ≡ 1 [MOD 2] :=
    Nat.ModEq.mul_left_cancel'
      (Nat.ne_of_gt (Arithmetic.twoPow_pos D)) hScaled'
  have htMod : t % 2 = 1 := by
    change t % 2 = 1 % 2 at htModEq
    simpa using htModEq
  have htPos : 0 < t := by
    have htNe : t ≠ 0 := by
      intro htZero
      subst t
      norm_num at htMod
    exact Nat.pos_of_ne_zero htNe
  have hDK : D ≤ K := by
    have hRoof := SInf.prefixDepth_le_beatty m
    dsimp [D, K]
    omega
  have hK : D + E = K := by
    dsimp [D, E, K, endpointCompletionExtraDepth]
    exact Nat.add_sub_of_le hDK
  have hCLt : C < 2 ^ (K + 1) := by
    simpa [C, K] using O.endpointCompletionStart_lt_fullModulus SInf hm
  have hMulLt :
      2 ^ D * t < 2 ^ D * 2 ^ (E + 1) := by
    calc
      2 ^ D * t ≤ C := by rw [hStart']; omega
      _ < 2 ^ (K + 1) := hCLt
      _ = 2 ^ D * 2 ^ (E + 1) := by
            rw [← hK]
            rw [show D + E + 1 = D + (E + 1) by omega, pow_add]
  have htLt : t < 2 ^ (E + 1) :=
    (Nat.mul_lt_mul_left (Arithmetic.twoPow_pos D)).mp hMulLt
  have hEndpoint :=
    O.endpointCompletion_endpoint_eq_of_start_lift SInf hm
      (by simpa [C, x, D] using hStart')
  refine ⟨t, ?_, htPos, htMod, ?_, ?_⟩
  · simpa [C, x, D] using hStart'
  · simpa [E] using htLt
  · exact hEndpoint

/-- natural completion lift coefficient は start equation だけで一意。 -/
theorem endpointCompletionNatLift_unique
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (ht :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hu :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * u) :
    t = u := by
  have hSum :
      O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * u :=
    ht.symm.trans hu
  have hMul :
      2 ^ infinitePrefixDepth O.exponent m * t =
        2 ^ infinitePrefixDepth O.exponent m * u :=
    Nat.add_left_cancel hSum
  exact
    Nat.mul_left_cancel
      (Arithmetic.twoPow_pos (infinitePrefixDepth O.exponent m)) hMul


/--
`m` が actual start より十分先なら、自動的に `x < 2^D_m`。

自然数 start の binary expansion が有限であることを、odd-block endpoint depth だけで使う形。
-/
theorem start_lt_twoPow_infinitePrefixDepth_of_start_succ_le
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    O.value 0 < 2 ^ infinitePrefixDepth O.exponent m := by
  let x := O.value 0
  let D := infinitePrefixDepth O.exponent m
  have hxSelf : x < 2 ^ x := by
    exact x.lt_two_pow_self
  have hxm' : x ≤ m := by
    dsimp [x] at hxm ⊢
    omega
  have hPowXM : 2 ^ x ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hxm'
  have hmD : m ≤ D := by
    dsimp [D]
    exact O.index_le_infinitePrefixDepth SInf m
  have hPowMD : 2 ^ m ≤ 2 ^ D :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hmD
  exact lt_of_lt_of_le hxSelf (le_trans hPowXM hPowMD)

/--
`m ≥ x+1` なら natural completion lift は無条件で存在する。
前定理の `x < 2^D_m` 仮定を、明示的な endpoint index bound に置き換えた wrapper。
-/
theorem exists_endpointCompletionNatLift_of_start_succ_le
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < m) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t ∧
      0 < t ∧
      t % 2 = 1 ∧
      t < 2 ^ (O.endpointCompletionExtraDepth m + 1) ∧
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
  let hm : 0 < m := by omega
  have hx :=
    O.start_lt_twoPow_infinitePrefixDepth_of_start_succ_le SInf hxm
  simpa [hm] using O.exists_endpointCompletionNatLift SInf hm hx

/--
十分先の natural completion lift を survivor defect 座標だけで書いた形。

`E_m = δ_m+1` を代入し、lift coefficient の上界は `2^(δ_m+2)` になる。
-/
theorem exists_endpointCompletionNatLift_defect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hxm : O.value 0 + 1 ≤ m) :
    ∃ t : ℕ,
      O.endpointCompletionStart SInf (by omega : 0 < m) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t ∧
      0 < t ∧
      t % 2 = 1 ∧
      t < 2 ^ (infiniteSurvivorDefect O.exponent m + 2) ∧
      2 ^ (infiniteSurvivorDefect O.exponent m + 1) *
          O.endpointCompletionEnd SInf (by omega : 0 < m) =
        O.value m + 3 ^ m * t := by
  let hm : 0 < m := by omega
  rcases O.exists_endpointCompletionNatLift_of_start_succ_le SInf hxm with
    ⟨t, hStart, htPos, htOdd, htBound, hEndpoint⟩
  have hE := O.endpointCompletionExtraDepth_eq_defect_add_one SInf m
  refine ⟨t, ?_, htPos, htOdd, ?_, ?_⟩
  · simpa [hm] using hStart
  · rw [hE] at htBound
    simpa [Nat.add_assoc] using htBound
  · rw [hE] at hEndpoint
    simpa using hEndpoint

/--
completion endpoint bridge の Hensel residue 形。

`Y_m` が奇数なので `2^E_m Y_m` は modulo `2^(E_m+1)` で exactly `2^E_m`。
-/
theorem endpointCompletionLift_henselModEq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hEndpoint :
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf hm =
        O.value m + 3 ^ m * t) :
    O.value m + 3 ^ m * t ≡
      2 ^ O.endpointCompletionExtraDepth m
      [MOD 2 ^ (O.endpointCompletionExtraDepth m + 1)] := by
  let E := O.endpointCompletionExtraDepth m
  let Y := O.endpointCompletionEnd SInf hm
  have hOdd : Odd Y := by
    simpa [Y] using O.endpointCompletionEnd_odd SInf hm
  rcases hOdd with ⟨q, hq⟩
  rw [← hEndpoint]
  change
    (2 ^ E * Y) % 2 ^ (E + 1) =
      (2 ^ E) % 2 ^ (E + 1)
  have hLt : 2 ^ E < 2 ^ (E + 1) := by
    rw [pow_succ]
    have hPos := Arithmetic.twoPow_pos E
    omega
  rw [Nat.mod_eq_of_lt hLt]
  rw [hq]
  have hExpand :
      2 ^ E * (2 * q + 1) =
        2 ^ E + 2 ^ (E + 1) * q := by
    rw [pow_succ]
    ring
  rw [hExpand, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hLt

/-- defect 座標で書いた Hensel residue。 -/
theorem endpointCompletionLift_henselModEq_defect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (hm : 0 < m)
    (hEndpoint :
      2 ^ O.endpointCompletionExtraDepth m *
          O.endpointCompletionEnd SInf hm =
        O.value m + 3 ^ m * t) :
    O.value m + 3 ^ m * t ≡
      2 ^ (infiniteSurvivorDefect O.exponent m + 1)
      [MOD 2 ^ (infiniteSurvivorDefect O.exponent m + 2)] := by
  have h := O.endpointCompletionLift_henselModEq SInf hm hEndpoint
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
  simpa [Nat.add_assoc] using h

/--
異なる二つの completion canonical starts の最初の相違 bit は、早い側の actual depth `D_r`。

これは completion family の exact ultrametric law。
-/
theorem endpointCompletionStart_pair_exact_twoDepth
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {r s : ℕ}
    (hr : 0 < r)
    (hrs : r < s) :
    (O.endpointCompletionStart SInf hr ≡
      O.endpointCompletionStart SInf (lt_trans hr hrs)
      [MOD 2 ^ infinitePrefixDepth O.exponent r]) ∧
    ¬ (O.endpointCompletionStart SInf hr ≡
      O.endpointCompletionStart SInf (lt_trans hr hrs)
      [MOD 2 ^ (infinitePrefixDepth O.exponent r + 1)]) := by
  let Dr := infinitePrefixDepth O.exponent r
  let Ds := infinitePrefixDepth O.exponent s
  let Cr := O.endpointCompletionStart SInf hr
  let Cs := O.endpointCompletionStart SInf (lt_trans hr hrs)
  let x := O.value 0
  have hDepth : Dr < Ds := by
    simpa [Dr, Ds] using O.infinitePrefixDepth_lt_of_lt SInf hrs
  have hCrLow : Cr ≡ x [MOD 2 ^ Dr] := by
    simpa [Cr, x, Dr] using O.endpointCompletionStart_modEq_start SInf hr
  have hCsLowFull : Cs ≡ x [MOD 2 ^ Ds] := by
    simpa [Cs, x, Ds] using
      O.endpointCompletionStart_modEq_start SInf (lt_trans hr hrs)
  have hPowLow : 2 ^ Dr ∣ 2 ^ Ds :=
    Nat.pow_dvd_pow 2 (Nat.le_of_lt hDepth)
  have hCsLow : Cs ≡ x [MOD 2 ^ Dr] :=
    hCsLowFull.of_dvd hPowLow
  have hPairLow : Cr ≡ Cs [MOD 2 ^ Dr] :=
    hCrLow.trans hCsLow.symm
  have hCrHigh : Cr ≡ x + 2 ^ Dr [MOD 2 ^ (Dr + 1)] := by
    simpa [Cr, x, Dr] using
      O.endpointCompletionStart_modEq_start_add_twoPow SInf hr
  have hDepthHigh : Dr + 1 ≤ Ds := by omega
  have hPowHigh : 2 ^ (Dr + 1) ∣ 2 ^ Ds :=
    Nat.pow_dvd_pow 2 hDepthHigh
  have hCsHigh : Cs ≡ x [MOD 2 ^ (Dr + 1)] :=
    hCsLowFull.of_dvd hPowHigh
  have hPairHigh :
      ¬ Cr ≡ Cs [MOD 2 ^ (Dr + 1)] := by
    intro hSame
    have hBad : x ≡ x + 2 ^ Dr [MOD 2 ^ (Dr + 1)] :=
      hCsHigh.symm.trans (hSame.symm.trans hCrHigh)
    have hDiv : 2 ^ (Dr + 1) ∣ 2 ^ Dr := by
      have hLe : x ≤ x + 2 ^ Dr := by omega
      simpa using (Nat.modEq_iff_dvd' hLe).mp hBad
    have hLePow : 2 ^ (Dr + 1) ≤ 2 ^ Dr :=
      Nat.le_of_dvd (Arithmetic.twoPow_pos Dr) hDiv
    rw [pow_succ] at hLePow
    have hPos := Arithmetic.twoPow_pos Dr
    omega
  simpa [Cr, Cs, Dr] using And.intro hPairLow hPairHigh

end OddOrbit
end Collatz3
