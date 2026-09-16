import CollatzLean.Collatz3.CSTConditional.FutureMinimumEndpointPhase
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.Canonical.AffineDataREQ
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: future-minimum block completion cocycle

前段では completion branch を一歩ごとに actual-compatible に選ぶと、その整数 branch digit が
一意であることを得た。

ここでは内部 step を追わず、future minimum `i` から次の future minimum `j` までを
一つの block として扱う。

`r = j-i`, `H = beattyIndex r`, `δ = defect i`,
`c = beattyCarry i r ∈ {0,1}` とすると Global CST 下では

* block total two-depth は exact に `H`,
* endpoint defect は `δ+c`。

両端 natural completion lift を `t,u`、completion endpoint を `Y_i,Y_j` とすると

`Q = 2^H u - t`

に対して exact に

`3^j Q + B
 = 2^(δ+1) (2^(H+c) Y_j - 3^r Y_i)`

が成り立つ。右括弧は odd なので、`Q` は法 `2^(δ+2)` 上で
affine data `(j,δ+1,B)` の canonical start class に属する。

従って defect scale で割ると

`Q / 2^δ = R / 2^δ + 4 J`

という block branch digit `J : ℤ` が存在する。

新しい block state / branch type / residue definition は導入しない。
`R` には既存 `canonicalStartOfAffineData` をそのまま使う。
-/

namespace Collatz3
namespace Bridge

/--
affine data の canonical start を `Int.ModEq` で読んだ薄い wrapper。

`3^p R + B ≡ 2^H (mod 2^(H+1))`。
-/
theorem canonicalStartOfAffineData_intModEq
    (p H B : ℕ) :
    (3 : ℤ) ^ p * (canonicalStartOfAffineData p H B : ℤ) + (B : ℤ) ≡
      (2 : ℤ) ^ H [ZMOD (2 : ℤ) ^ (H + 1)] := by
  let R := canonicalStartOfAffineData p H B
  let Y := canonicalEndOfAffineData p H B
  have hEqNat := reqEquationOfAffineData p H B
  have hEq0 :
      (2 : ℤ) ^ H * (canonicalEndOfAffineData p H B : ℤ) =
        (3 : ℤ) ^ p * (canonicalStartOfAffineData p H B : ℤ) + (B : ℤ) := by
    exact_mod_cast hEqNat
  have hEq :
      (2 : ℤ) ^ H * (Y : ℤ) =
        (3 : ℤ) ^ p * (R : ℤ) + (B : ℤ) := by
    simpa [R, Y] using hEq0
  rcases canonicalEndOfAffineData_odd p H B with ⟨k, hk⟩
  have hY : (Y : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hk
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨-(k : ℤ), ?_⟩
  change
    (2 : ℤ) ^ H =
      ((3 : ℤ) ^ p * (R : ℤ) + (B : ℤ)) +
        (2 : ℤ) ^ (H + 1) * (-(k : ℤ))
  rw [← hEq, hY, pow_succ]
  ring

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

/--
next-future-minimum block の natural completion lift を両端で比較した exact cocycle。

`r=j-i`, `H=beattyIndex r`, `c=beattyCarry i r` とすると

`3^j (2^H u-t) + B
 = 2^(δ_i+1) (2^(H+c)Y_j - 3^rY_i)`。
-/
theorem nextFutureMinimum_completionBlock_cocycle_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartJ :
      O.endpointCompletionStart SInf (lt_trans hi hNext.1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u) :
    (3 : ℤ) ^ j *
          (((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ)) +
        (Word.affineConst (O.segmentWord i (j - i)) : ℤ) =
      (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 1) *
        ((2 : ℤ) ^
              (Critical.beattyIndex (j - i) +
                Critical.beattyCarry i (j - i)) *
            (O.endpointCompletionEnd SInf (lt_trans hi hNext.1) : ℤ) -
          (3 : ℤ) ^ (j - i) *
            (O.endpointCompletionEnd SInf hi : ℤ)) := by
  let r := j - i
  let H := Critical.beattyIndex r
  let c := Critical.beattyCarry i r
  let δ := infiniteSurvivorDefect O.exponent i
  let Yi := O.endpointCompletionEnd SInf hi
  let Yj := O.endpointCompletionEnd SInf (lt_trans hi hNext.1)
  let B := Word.affineConst (O.segmentWord i r)
  have hij : i < j := hNext.1
  have hIndex : i + r = j := by
    dsimp [r]
    omega
  have hDepth :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  have hDef :=
    O.nextFutureMinimum_defect_eq_add_carry_of_globalCST
      G SInf hStart hNext
  have hActualNat :=
    (Word.endpointEquation_iff
      (O.segmentWord i r) (O.value i) (O.value (i + r))).1
      (O.runsSegment i r).endpointEquation
  have hOdd := O.segmentWord_oddSteps i r
  have hActualNat' :
      2 ^ H * O.value j = 3 ^ r * O.value i + B := by
    rw [hIndex] at hActualNat
    dsimp [H, B]
    simpa [r, hDepth, hOdd] using hActualNat
  have hActual :
      (2 : ℤ) ^ H * (O.value j : ℤ) =
        (3 : ℤ) ^ r * (O.value i : ℤ) + (B : ℤ) := by
    exact_mod_cast hActualNat'
  have hEndINat :=
    O.endpointCompletion_endpoint_eq_of_start_lift SInf hi hStartI
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf i] at hEndINat
  have hEndI :
      (3 : ℤ) ^ i * (t : ℤ) =
        (2 : ℤ) ^ (δ + 1) * (Yi : ℤ) - (O.value i : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hEndINat
    push_cast at h
    dsimp [δ, Yi] at h ⊢
    linarith
  have hEndJNat :=
    O.endpointCompletion_endpoint_eq_of_start_lift
      SInf (lt_trans hi hNext.1) hStartJ
  rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf j] at hEndJNat
  have hEndJ :
      (3 : ℤ) ^ j * (u : ℤ) =
        (2 : ℤ) ^
            (infiniteSurvivorDefect O.exponent j + 1) * (Yj : ℤ) -
          (O.value j : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hEndJNat
    push_cast at h
    dsimp [Yj] at h ⊢
    linarith
  have hDef' :
      infiniteSurvivorDefect O.exponent j = δ + c := by
    simpa [δ, c, r] using hDef
  have hPow :
      (2 : ℤ) ^ H *
          (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent j + 1) =
        (2 : ℤ) ^ (δ + 1) * (2 : ℤ) ^ (H + c) := by
    rw [hDef']
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  change
    (3 : ℤ) ^ j *
          (((2 ^ H * u : ℕ) : ℤ) - (t : ℤ)) + (B : ℤ) =
      (2 : ℤ) ^ (δ + 1) *
        ((2 : ℤ) ^ (H + c) * (Yj : ℤ) -
          (3 : ℤ) ^ r * (Yi : ℤ))
  push_cast
  calc
    (3 : ℤ) ^ j *
          ((2 : ℤ) ^ H * (u : ℤ) - (t : ℤ)) + (B : ℤ)
        =
      (2 : ℤ) ^ H * ((3 : ℤ) ^ j * (u : ℤ)) -
        (3 : ℤ) ^ r * ((3 : ℤ) ^ i * (t : ℤ)) + (B : ℤ) := by
          rw [← hIndex, pow_add]
          ring
    _ =
      (2 : ℤ) ^ H *
          ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent j + 1) *
              (Yj : ℤ) - (O.value j : ℤ)) -
        (3 : ℤ) ^ r *
          ((2 : ℤ) ^ (δ + 1) * (Yi : ℤ) - (O.value i : ℤ)) +
        (B : ℤ) := by
          rw [hEndI, hEndJ]
    _ =
      (2 : ℤ) ^ (δ + 1) *
        ((2 : ℤ) ^ (H + c) * (Yj : ℤ) -
          (3 : ℤ) ^ r * (Yi : ℤ)) := by
      linear_combination (Yj : ℤ) * hPow - hActual

/--
block cocycle 右辺の cofactor は odd。

`H>0` なので最初の項は even、`3^r Y_i` は odd であり、差は odd になる。
-/
theorem nextFutureMinimum_completionBlock_factor_odd_of_globalCST
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hi : 0 < i)
    (hNext : O.NextFutureMinimum i j) :
    Odd
      ((2 : ℤ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) *
          (O.endpointCompletionEnd SInf (lt_trans hi hNext.1) : ℤ) -
        (3 : ℤ) ^ (j - i) *
          (O.endpointCompletionEnd SInf hi : ℤ)) := by
  let r := j - i
  let H := Critical.beattyIndex r
  let c := Critical.beattyCarry i r
  have hij : i < j := hNext.1
  have hr : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hij
  have hH : 0 < H + c := by
    have hLe := index_le_beattyIndex r
    dsimp [H]
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hH)
  rcases O.endpointCompletionEnd_odd SInf hi with ⟨a, ha⟩
  rcases O.endpointCompletionEnd_odd SInf (lt_trans hi hNext.1) with ⟨b, hb⟩
  rcases threePow_odd_nat r with ⟨q, hq⟩
  refine
    ⟨(2 : ℤ) ^ d * (2 * (b : ℤ) + 1) -
        (2 * (q : ℤ) * (a : ℤ) + (q : ℤ) + (a : ℤ)) - 1, ?_⟩
  change
    (2 : ℤ) ^ (H + c) *
          (O.endpointCompletionEnd SInf (lt_trans hi hNext.1) : ℤ) -
        (3 : ℤ) ^ r * (O.endpointCompletionEnd SInf hi : ℤ) =
      2 *
          ((2 : ℤ) ^ d * (2 * (b : ℤ) + 1) -
            (2 * (q : ℤ) * (a : ℤ) + (q : ℤ) + (a : ℤ)) - 1) + 1
  have hqZ :
      (3 : ℤ) ^ r = 2 * (q : ℤ) + 1 := by
    exact_mod_cast hq
  change
    (2 : ℤ) ^ (H + c) *
          (O.endpointCompletionEnd SInf (lt_trans hi hNext.1) : ℤ) -
        (3 : ℤ) ^ r * (O.endpointCompletionEnd SInf hi : ℤ) =
      2 *
          ((2 : ℤ) ^ d * (2 * (b : ℤ) + 1) -
            (2 * (q : ℤ) * (a : ℤ) + (q : ℤ) + (a : ℤ)) - 1) + 1
  rw [hd, pow_succ, ha, hb, hqZ]
  push_cast
  ring

/--
block lift `Q=2^H u-t` が満たす有限 Hensel congruence。

`3^j Q + B ≡ 2^(δ+1) (mod 2^(δ+2))`。
-/
theorem nextFutureMinimum_completionBlock_hensel_modEq_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartJ :
      O.endpointCompletionStart SInf (lt_trans hi hNext.1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u) :
    (3 : ℤ) ^ j *
          (((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ)) +
        (Word.affineConst (O.segmentWord i (j - i)) : ℤ) ≡
      (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 1)
      [ZMOD (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 2)] := by
  let F : ℤ :=
    (2 : ℤ) ^
          (Critical.beattyIndex (j - i) +
            Critical.beattyCarry i (j - i)) *
        (O.endpointCompletionEnd SInf (lt_trans hi hNext.1) : ℤ) -
      (3 : ℤ) ^ (j - i) *
        (O.endpointCompletionEnd SInf hi : ℤ)
  have hCoc :=
    O.nextFutureMinimum_completionBlock_cocycle_of_globalCST
      G SInf hi hStart hNext hStartI hStartJ
  have hOdd : Odd F := by
    simpa [F] using
      O.nextFutureMinimum_completionBlock_factor_odd_of_globalCST SInf hi hNext
  rcases hOdd with ⟨q, hq⟩
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨-(q : ℤ), ?_⟩
  rw [hCoc]
  change
    (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 1) =
      (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 1) * F +
        (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 2) * (-(q : ℤ))
  rw [hq]
  rw [show infiniteSurvivorDefect O.exponent i + 2 =
      (infiniteSurvivorDefect O.exponent i + 1) + 1 by omega, pow_succ]
  ring

/--
block lift `Q` は既存 affine canonical start `R(j,δ+1,B)` と
modulo `2^(δ+2)` で一致する。
-/
theorem nextFutureMinimum_completionBlock_modEq_canonicalAffineStart_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartJ :
      O.endpointCompletionStart SInf (lt_trans hi hNext.1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u) :
    (((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ)) ≡
      (canonicalStartOfAffineData
        j (infiniteSurvivorDefect O.exponent i + 1)
        (Word.affineConst (O.segmentWord i (j - i))) : ℤ)
      [ZMOD (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent i + 2)] := by
  let δ := infiniteSurvivorDefect O.exponent i
  let B := Word.affineConst (O.segmentWord i (j - i))
  let Q : ℤ :=
    ((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ)
  let R : ℤ := canonicalStartOfAffineData j (δ + 1) B
  have hQ :=
    O.nextFutureMinimum_completionBlock_hensel_modEq_of_globalCST
      G SInf hi hStart hNext hStartI hStartJ
  have hR0 := Bridge.canonicalStartOfAffineData_intModEq j (δ + 1) B
  have hR :
      (3 : ℤ) ^ j * R + (B : ℤ) ≡
        (2 : ℤ) ^ (δ + 1) [ZMOD (2 : ℤ) ^ (δ + 2)] := by
    simpa [R, Nat.add_assoc] using hR0
  have hQ' :
      (3 : ℤ) ^ j * Q + (B : ℤ) ≡
        (2 : ℤ) ^ (δ + 1) [ZMOD (2 : ℤ) ^ (δ + 2)] := by
    simpa [Q, B, δ] using hQ
  have hSum :
      (3 : ℤ) ^ j * Q + (B : ℤ) ≡
        (3 : ℤ) ^ j * R + (B : ℤ)
        [ZMOD (2 : ℤ) ^ (δ + 2)] := by
    exact hQ'.trans hR.symm
  have hMul :
      (3 : ℤ) ^ j * Q ≡ (3 : ℤ) ^ j * R
        [ZMOD (2 : ℤ) ^ (δ + 2)] :=
    Int.ModEq.add_right_cancel' (B : ℤ) hSum
  have hCancel :
      Q ≡ R [ZMOD (2 : ℤ) ^ (δ + 2)] :=
    Bridge.cancel_threePow_modEq_lattice hMul
  simpa [Q, R, B, δ] using hCancel

/--
future-minimum block の actual natural lift に対応する normalized block branch digit が存在する。

`Q/2^δ = R/2^δ + 4J` かつ同時に
`Q/2^δ = 2^(H+c) tau_j - tau_i`。
-/
theorem exists_nextFutureMinimum_normalizedCompletionBlockBranchDigit_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartJ :
      O.endpointCompletionStart SInf (lt_trans hi hNext.1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u) :
    ∃ J : ℤ,
      ((((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ) : ℤ) : ℝ) /
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i =
          (canonicalStartOfAffineData
              j (infiniteSurvivorDefect O.exponent i + 1)
              (Word.affineConst (O.segmentWord i (j - i))) : ℝ) /
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i +
            4 * (J : ℝ) ∧
      ((((2 ^ Critical.beattyIndex (j - i) * u : ℕ) : ℤ) - (t : ℤ) : ℤ) : ℝ) /
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i =
          (2 : ℝ) ^
              (Critical.beattyIndex (j - i) +
                Critical.beattyCarry i (j - i)) *
              O.normalizedCompletionLiftCoefficient j u -
            O.normalizedCompletionLiftCoefficient i t := by
  let δ := infiniteSurvivorDefect O.exponent i
  let H := Critical.beattyIndex (j - i)
  let c := Critical.beattyCarry i (j - i)
  let B := Word.affineConst (O.segmentWord i (j - i))
  let Q : ℤ := ((2 ^ H * u : ℕ) : ℤ) - (t : ℤ)
  let R : ℤ := canonicalStartOfAffineData j (δ + 1) B
  have hMod :=
    O.nextFutureMinimum_completionBlock_modEq_canonicalAffineStart_of_globalCST
      G SInf hi hStart hNext hStartI hStartJ
  have hMod' : Q ≡ R [ZMOD (2 : ℤ) ^ (δ + 2)] := by
    simpa [Q, R, B, H, δ] using hMod
  rcases Int.modEq_iff_add_fac.mp hMod' with ⟨k, hk⟩
  let J : ℤ := -k
  have hQ : Q = R + (2 : ℤ) ^ (δ + 2) * J := by
    dsimp [J]
    rw [hk]
    ring
  have hNorm :
      (Q : ℝ) / (2 : ℝ) ^ δ =
        (R : ℝ) / (2 : ℝ) ^ δ + 4 * (J : ℝ) := by
    have hQR := congrArg (fun z : ℤ => (z : ℝ)) hQ
    push_cast at hQR
    have hPow : (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
      rw [pow_add]
      norm_num
      ring
    rw [hPow] at hQR
    field_simp
    nlinarith [hQR]
  have hDef :=
    O.nextFutureMinimum_defect_eq_add_carry_of_globalCST
      G SInf hStart hNext
  have hLift :
      (Q : ℝ) / (2 : ℝ) ^ δ =
        (2 : ℝ) ^ (H + c) * O.normalizedCompletionLiftCoefficient j u -
          O.normalizedCompletionLiftCoefficient i t := by
    unfold normalizedCompletionLiftCoefficient
    dsimp [Q, H, c, δ]
    push_cast
    have hDef' :
        infiniteSurvivorDefect O.exponent j = δ + c := by
      simpa [δ, c] using hDef
    rw [hDef']
    have hPow :
        (2 : ℝ) ^ H * (2 : ℝ) ^ (δ + c) =
          (2 : ℝ) ^ δ * (2 : ℝ) ^ (H + c) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hScale :
        (2 : ℝ) ^ H / (2 : ℝ) ^ δ =
          (2 : ℝ) ^ (H + c) / (2 : ℝ) ^ (δ + c) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      simpa [mul_comm] using hPow
    calc
      ((2 : ℝ) ^ H * (u : ℝ) - (t : ℝ)) / (2 : ℝ) ^ δ
          = ((2 : ℝ) ^ H / (2 : ℝ) ^ δ) * (u : ℝ) -
              (t : ℝ) / (2 : ℝ) ^ δ := by ring
      _ = ((2 : ℝ) ^ (H + c) / (2 : ℝ) ^ (δ + c)) * (u : ℝ) -
              (t : ℝ) / (2 : ℝ) ^ δ := by rw [hScale]
      _ = (2 : ℝ) ^ (H + c) *
              ((u : ℝ) / (2 : ℝ) ^ (δ + c)) -
            (t : ℝ) / (2 : ℝ) ^ δ := by ring
  refine ⟨J, ?_, ?_⟩
  · simpa [Q, R, B, H, δ] using hNorm
  · simpa [Q, H, c, δ] using hLift

end OddOrbit
end Collatz3
