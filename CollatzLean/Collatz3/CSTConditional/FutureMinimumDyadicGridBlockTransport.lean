import CollatzLean.Collatz3.CSTConditional.FutureMinimumCompletionBlockBranchUniqueness
import CollatzLean.Collatz3.CSTConditional.FutureMinimumIntegralCompletionLattice
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: future-minimum dyadic defect-grid の block transport

Stage 5/6 は completion lift 側を block 全体で処理した。
ここでは dyadic state `xi = Z / 2^δ` の整数分子 `Z` を、
future minimum から次の future minimum まで直接運ぶ。

future minimum では actual value は `3 mod 4` なので

`A_m := (value(m)+1)/4`

を整数座標として使える。block 長 `r=j-i`、total two-depth `H=beattyIndex r`、
affine constant `B` に対し

`2^H value(j) = 3^r value(i) + B`

を `A` 座標へ移すと

`4 C = 2^H - 3^r + B`,
`C = 2^H A_j - 3^r A_i`

という整数 correction が得られる。

一方、future-minimum integral completion lattice は

`a_i' + 3^i Z_i ≡ 0 (mod 2^δ_i)`

を与える。actual quarter `A_m` と residue quarter `(a_m+1)/4` は
modulo `2^δ_m` で一致するので、両端を block equation に代入すると

`3^j (Z_i - 2^H Z_j) ≡ C (mod 2^δ_i)`

を得る。

新しい `C` 座標や `Z` state は定義せず、すべて existential / derived theorem として保存する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
future minimum では `(value+1)/4` と `(defectActualResidue+1)/4` の差は
exact に `2^δ * ordinaryQuotient`。
-/
theorem futureMinimum_quarterValue_eq_residueQuarter_add
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hMin : O.FutureMinimumAt m) :
    (O.value m + 1) / 4 =
      (O.defectActualResidue m + 1) / 4 +
        2 ^ infiniteSurvivorDefect O.exponent m * O.defectActualQuotient m := by
  let δ := infiniteSurvivorDefect O.exponent m
  let a := O.defectActualResidue m
  let q := O.defectActualQuotient m
  have he : O.exponent m = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor SInf hMin
  have hxMod : O.value m % 4 = 3 :=
    O.value_mod_four_eq_three_of_exponent_eq_one he
  have haMod : a % 4 = 3 := by
    simpa [a] using
      O.futureMinimum_defectActualResidue_mod_four_eq_three SInf hMin
  have hxDecomp : O.value m + 1 = 4 * ((O.value m + 1) / 4) := by
    omega
  have haDecomp : a + 1 = 4 * ((a + 1) / 4) := by
    omega
  have hValue := O.value_eq_defectActualResidue_add_modulus_mul_quotient m
  have hValue' :
      O.value m = a + 2 ^ (δ + 2) * q := by
    simpa [a, q, δ] using hValue
  have hPow : 2 ^ (δ + 2) = 4 * 2 ^ δ := by
    rw [pow_add]
    norm_num
    ring
  have hMain :
      O.value m + 1 =
        4 * (((a + 1) / 4) + 2 ^ δ * q) := by
    calc
      O.value m + 1 = a + 2 ^ (δ + 2) * q + 1 := by rw [hValue']
      _ = (a + 1) + 2 ^ (δ + 2) * q := by ring
      _ = 4 * ((a + 1) / 4) + (4 * 2 ^ δ) * q := by
            rw [haDecomp, hPow]
            simp
      _ = 4 * (((a + 1) / 4) + 2 ^ δ * q) := by ring
  have hFour :
      4 * ((O.value m + 1) / 4) =
        4 * (((a + 1) / 4) + 2 ^ δ * q) := by
    rw [← hxDecomp, hMain]
  have hCancel := Nat.mul_left_cancel (by norm_num : 0 < (4 : ℕ)) hFour
  simpa [a, q, δ] using hCancel

/--
前定理を有限合同として読む。

`(value+1)/4 ≡ (residue+1)/4 (mod 2^δ)`。
-/
theorem futureMinimum_quarterValue_modEq_residueQuarter
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hMin : O.FutureMinimumAt m) :
    (((O.value m + 1) / 4 : ℕ) : ℤ) ≡
      (((O.defectActualResidue m + 1) / 4 : ℕ) : ℤ)
      [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent m] := by
  have hNat := O.futureMinimum_quarterValue_eq_residueQuarter_add SInf hMin
  have hZ :
      (((O.value m + 1) / 4 : ℕ) : ℤ) =
        (((O.defectActualResidue m + 1) / 4 : ℕ) : ℤ) +
          (2 : ℤ) ^ infiniteSurvivorDefect O.exponent m *
            (O.defectActualQuotient m : ℤ) := by
    exact_mod_cast hNat
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨-(O.defectActualQuotient m : ℤ), ?_⟩
  rw [hZ]
  ring

/--
actual next-future-minimum block を `(value+1)/4` 座標へ移した exact identity。

`C = 2^H A_j - 3^r A_i` と置けば
`4C = 2^H - 3^r + B`。
-/
theorem exists_nextFutureMinimum_quarterCorrection_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hEnd : O.FutureMinimumAt j)
    (hNext : O.NextFutureMinimum i j) :
    ∃ C : ℤ,
      C =
        (2 : ℤ) ^ Critical.beattyIndex (j - i) *
            (((O.value j + 1) / 4 : ℕ) : ℤ) -
          (3 : ℤ) ^ (j - i) *
            (((O.value i + 1) / 4 : ℕ) : ℤ) ∧
      4 * C =
        (2 : ℤ) ^ Critical.beattyIndex (j - i) -
          (3 : ℤ) ^ (j - i) +
          (Word.affineConst (O.segmentWord i (j - i)) : ℤ) := by
  let r := j - i
  let H := Critical.beattyIndex r
  let B := Word.affineConst (O.segmentWord i r)
  let Ai := (O.value i + 1) / 4
  let Aj := (O.value j + 1) / 4
  have hij : i < j := hNext.1
  have hIndex : i + r = j := by
    dsimp [r]
    omega
  have hDepth :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  have hActualNat :=
    (Word.endpointEquation_iff
      (O.segmentWord i r) (O.value i) (O.value (i + r))).1
      (O.runsSegment i r).endpointEquation
  have hOdd := O.segmentWord_oddSteps i r
  have hDepthR :
      (O.segmentWord i r).twoSteps = Critical.beattyIndex r := by
    simpa [r] using hDepth
  have hActualNat' :
      2 ^ H * O.value j = 3 ^ r * O.value i + B := by
    rw [hIndex] at hActualNat
    dsimp [H, B]
    simpa [hDepthR, hOdd] using hActualNat
  have hActual :
      (2 : ℤ) ^ H * (O.value j : ℤ) =
        (3 : ℤ) ^ r * (O.value i : ℤ) + (B : ℤ) := by
    exact_mod_cast hActualNat'
  have hei : O.exponent i = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor SInf hStart
  have hej : O.exponent j = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor SInf hEnd
  have hiMod : O.value i % 4 = 3 :=
    O.value_mod_four_eq_three_of_exponent_eq_one hei
  have hjMod : O.value j % 4 = 3 :=
    O.value_mod_four_eq_three_of_exponent_eq_one hej
  have hAiNat : O.value i + 1 = 4 * Ai := by
    dsimp [Ai]
    omega
  have hAjNat : O.value j + 1 = 4 * Aj := by
    dsimp [Aj]
    omega
  have hAiCast : (O.value i : ℤ) + 1 = 4 * (Ai : ℤ) := by
    exact_mod_cast hAiNat
  have hAjCast : (O.value j : ℤ) + 1 = 4 * (Aj : ℤ) := by
    exact_mod_cast hAjNat
  have hAi : (O.value i : ℤ) = 4 * (Ai : ℤ) - 1 := by
    linarith
  have hAj : (O.value j : ℤ) = 4 * (Aj : ℤ) - 1 := by
    linarith
  let C : ℤ := (2 : ℤ) ^ H * (Aj : ℤ) - (3 : ℤ) ^ r * (Ai : ℤ)
  refine ⟨C, rfl, ?_⟩
  dsimp [C]
  rw [hAi, hAj] at hActual
  linear_combination hActual

/--
future-minimum dyadic grid の両端 Hensel congruenceと quarter block relation を合成した
`Z` block transport。

`3^j (Z_i - 2^H Z_j) ≡ C (mod 2^δ_i)`。
-/
theorem nextFutureMinimum_dyadicGrid_blockTransport_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hEnd : O.FutureMinimumAt j)
    (hNext : O.NextFutureMinimum i j)
    (Zi Zj C : ℤ)
    (hZi :
      (((O.defectActualResidue i + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ i * Zi ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i])
    (hZj :
      (((O.defectActualResidue j + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ j * Zj ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent j])
    (hC :
      C =
        (2 : ℤ) ^ Critical.beattyIndex (j - i) *
            (((O.value j + 1) / 4 : ℕ) : ℤ) -
          (3 : ℤ) ^ (j - i) *
            (((O.value i + 1) / 4 : ℕ) : ℤ)) :
    (3 : ℤ) ^ j *
        (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Zj) ≡
      C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i] := by
  let δ := infiniteSurvivorDefect O.exponent i
  let Ai : ℤ := (((O.defectActualResidue i + 1) / 4 : ℕ) : ℤ)
  let Aj : ℤ := (((O.defectActualResidue j + 1) / 4 : ℕ) : ℤ)
  let H := Critical.beattyIndex (j - i)
  let r := j - i
  have hDef :=
    O.nextFutureMinimum_defect_eq_add_carry_of_globalCST
      G SInf hStart hNext
  have hDiv :
      (2 : ℤ) ^ δ ∣
        (2 : ℤ) ^ infiniteSurvivorDefect O.exponent j := by
    refine ⟨(2 : ℤ) ^ Critical.beattyCarry i r, ?_⟩
    rw [hDef, pow_add]
  have hZi' :
      Ai + (3 : ℤ) ^ i * Zi ≡ 0 [ZMOD (2 : ℤ) ^ δ] := by
    simpa [Ai, δ] using hZi
  have hZjWeak0 := hZj.of_dvd hDiv
  have hZjWeak :
      Aj + (3 : ℤ) ^ j * Zj ≡ 0 [ZMOD (2 : ℤ) ^ δ] := by
    simpa [Aj, δ] using hZjWeak0
  have hiZero :
      Ai ≡ -((3 : ℤ) ^ i * Zi) [ZMOD (2 : ℤ) ^ δ] := by
    have htmp :
        Ai + (3 : ℤ) ^ i * Zi ≡
          -((3 : ℤ) ^ i * Zi) + (3 : ℤ) ^ i * Zi
          [ZMOD (2 : ℤ) ^ δ] := by
      simpa using hZi'
    exact Int.ModEq.add_right_cancel' ((3 : ℤ) ^ i * Zi) htmp
  have hjZero :
      Aj ≡ -((3 : ℤ) ^ j * Zj) [ZMOD (2 : ℤ) ^ δ] := by
    have htmp :
        Aj + (3 : ℤ) ^ j * Zj ≡
          -((3 : ℤ) ^ j * Zj) + (3 : ℤ) ^ j * Zj
          [ZMOD (2 : ℤ) ^ δ] := by
      simpa using hZjWeak
    exact Int.ModEq.add_right_cancel' ((3 : ℤ) ^ j * Zj) htmp
  have hActualResidue :
      (2 : ℤ) ^ H * Aj - (3 : ℤ) ^ r * Ai ≡
        C [ZMOD (2 : ℤ) ^ δ] := by
    -- quarter actual values と residue quarters の差は current modulus の倍数。
    have hiMod := O.futureMinimum_quarterValue_modEq_residueQuarter SInf hStart
    have hjModFull := O.futureMinimum_quarterValue_modEq_residueQuarter SInf hEnd
    have hjMod := hjModFull.of_dvd hDiv
    have hCombo :=
      (hjMod.mul_left ((2 : ℤ) ^ H)).sub
        (hiMod.mul_left ((3 : ℤ) ^ r))
    have hExact :
        (2 : ℤ) ^ H *
              (((O.value j + 1) / 4 : ℕ) : ℤ) -
            (3 : ℤ) ^ r *
              (((O.value i + 1) / 4 : ℕ) : ℤ) = C := by
      exact hC.symm
    rw [hExact] at hCombo
    simpa [Ai, Aj] using hCombo.symm
  have hSubst :=
    (hjZero.mul_left ((2 : ℤ) ^ H)).sub
      (hiZero.mul_left ((3 : ℤ) ^ r))
  have hRight :
      -((2 : ℤ) ^ H * ((3 : ℤ) ^ j * Zj)) -
          (-((3 : ℤ) ^ r * ((3 : ℤ) ^ i * Zi))) =
        (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Zj) := by
    have hIndex : i + r = j := by
      dsimp [r]
      exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
    rw [← hIndex, pow_add]
    ring
  have hToTarget :
      (2 : ℤ) ^ H * Aj - (3 : ℤ) ^ r * Ai ≡
        (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Zj)
        [ZMOD (2 : ℤ) ^ δ] := by
    calc
      (2 : ℤ) ^ H * Aj - (3 : ℤ) ^ r * Ai
          ≡
        (2 : ℤ) ^ H * (-((3 : ℤ) ^ j * Zj)) -
          (3 : ℤ) ^ r * (-((3 : ℤ) ^ i * Zi))
          [ZMOD (2 : ℤ) ^ δ] := hSubst
      _ =
        -((2 : ℤ) ^ H * ((3 : ℤ) ^ j * Zj)) -
          (-((3 : ℤ) ^ r * ((3 : ℤ) ^ i * Zi))) := by ring
      _ = (3 : ℤ) ^ j * (Zi - (2 : ℤ) ^ H * Zj) := hRight
  exact hToTarget.symm.trans hActualResidue

/--
canonical natural completions が両端で存在するとき、実際の `Zi,Zj` と quarter correction `C`
を同時に取り出せる package。
-/
theorem exists_nextFutureMinimum_dyadicGrid_blockTransport_package_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hEnd : O.FutureMinimumAt j)
    (hNext : O.NextFutureMinimum i j)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartJ :
      O.endpointCompletionStart SInf (lt_trans hi hNext.1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u) :
    ∃ Zi Zj C : ℤ,
      O.normalizedCompletionDyadicState i t =
          (Zi : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i ∧
      O.normalizedCompletionDyadicState j u =
          (Zj : ℝ) / (2 : ℝ) ^ infiniteSurvivorDefect O.exponent j ∧
      (((O.defectActualResidue i + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ i * Zi ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i] ∧
      (((O.defectActualResidue j + 1) / 4 : ℕ) : ℤ) +
          (3 : ℤ) ^ j * Zj ≡ 0
        [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent j] ∧
      4 * C =
        (2 : ℤ) ^ Critical.beattyIndex (j - i) -
          (3 : ℤ) ^ (j - i) +
          (Word.affineConst (O.segmentWord i (j - i)) : ℤ) ∧
      (3 : ℤ) ^ j *
          (Zi - (2 : ℤ) ^ Critical.beattyIndex (j - i) * Zj) ≡
        C [ZMOD (2 : ℤ) ^ infiniteSurvivorDefect O.exponent i] := by
  rcases
      O.exists_futureMinimum_dyadicState_defectGrid
        SInf hi hStart hStartI with ⟨Zi, hXiI, hZi⟩
  rcases
      O.exists_futureMinimum_dyadicState_defectGrid
        SInf (lt_trans hi hNext.1) hEnd hStartJ with ⟨Zj, hXiJ, hZj⟩
  rcases
      O.exists_nextFutureMinimum_quarterCorrection_of_globalCST
        G SInf hStart hEnd hNext with ⟨C, hCdef, hCid⟩
  have hTransport :=
    O.nextFutureMinimum_dyadicGrid_blockTransport_of_globalCST
      G SInf hStart hEnd hNext Zi Zj C hZi hZj hCdef
  exact ⟨Zi, Zj, C, hXiI, hXiJ, hZi, hZj, hCid, hTransport⟩

end OddOrbit
end Collatz3
