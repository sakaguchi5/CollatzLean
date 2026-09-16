import CollatzLean.Collatz3.CSTConditional.FutureMinimumCompletionBlockCocycle
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import Mathlib.Tactic.LinearCombination

/-!
# Collatz3 CSTConditional: future-minimum block branch の actual-compatible 一意性

Stage 5 で、next-future-minimum block 全体の normalized completion lift は

`rhoBlock + 4J = 2^(H+c) tau_j - tau_i`

と書けることを得た。

ここでは一歩版の branch uniqueness と同じ有限 actual compatibility を block 全体へ適用する。
二候補 `J₁,J₂` の差について

`4(J₁-J₂) = 2^(H+c)(tau₁-tau₂)`

であり、next endpoint の finite compatibility から

`3^j(tau₁-tau₂) = 4(z₁-z₂)`。

従って

`3^j(J₁-J₂) = 2^(H+c)(z₁-z₂)`

なので `2^(H+c)` が `J₁-J₂` を割る。一方 `tau₁,tau₂ ∈ (0,4)` から
`|J₁-J₂| < 2^(H+c)`。よって `J₁=J₂`。

新しい selector 関数は作らず、actual canonical block については `∃! J : ℤ` だけを保存する。
-/

namespace Collatz3
namespace Bridge

/--
任意の positive dyadic scale `2^K` に対する block branch digit 一意性。

finite actual compatibility と `(0,4)` bound だけを使う純粋な scalar theorem。
-/
theorem actualCompatible_normalizedCompletionBlockBranchDigit_unique
    (j K : ℕ)
    (tauCurrent rho tau₁ tau₂ theta : ℝ)
    (J₁ J₂ z₁ z₂ : ℤ)
    (hRec₁ :
      rho + 4 * (J₁ : ℝ) =
        (2 : ℝ) ^ K * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (J₂ : ℝ) =
        (2 : ℝ) ^ K * tau₂ - tauCurrent)
    (hTau₁ : 0 < tau₁ ∧ tau₁ < 4)
    (hTau₂ : 0 < tau₂ ∧ tau₂ < 4)
    (hCompat₁ :
      theta + ((3 : ℝ) ^ j / 4) * (tau₁ - 2) = (z₁ : ℝ))
    (hCompat₂ :
      theta + ((3 : ℝ) ^ j / 4) * (tau₂ - 2) = (z₂ : ℝ)) :
    J₁ = J₂ := by
  have hScalePos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hTauDiffLo : (-4 : ℝ) < tau₁ - tau₂ := by
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hTauDiffHi : tau₁ - tau₂ < 4 := by
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hRecDiff :
      (2 : ℝ) ^ K * (tau₁ - tau₂) =
        4 * (((J₁ - J₂ : ℤ) : ℝ)) := by
    push_cast
    linarith [hRec₁, hRec₂]
  have hLoScaled := mul_lt_mul_of_pos_left hTauDiffLo hScalePos
  have hHiScaled := mul_lt_mul_of_pos_left hTauDiffHi hScalePos
  have hJLoR :
      -((2 : ℝ) ^ K) < (((J₁ - J₂ : ℤ) : ℝ)) := by
    rw [hRecDiff] at hLoScaled
    nlinarith
  have hJHiR :
      (((J₁ - J₂ : ℤ) : ℝ)) < (2 : ℝ) ^ K := by
    rw [hRecDiff] at hHiScaled
    nlinarith
  have hCompatDiff :
      (3 : ℝ) ^ j * (tau₁ - tau₂) =
        4 * ((z₁ : ℝ) - (z₂ : ℝ)) := by
    linear_combination 4 * hCompat₁ - 4 * hCompat₂
  have hMainR :
      (3 : ℝ) ^ j * (((J₁ - J₂ : ℤ) : ℝ)) =
        (2 : ℝ) ^ K * (((z₁ - z₂ : ℤ) : ℝ)) := by
    have hComb :
        (3 : ℝ) ^ j *
            ((2 : ℝ) ^ K * (tau₁ - tau₂)) =
          (2 : ℝ) ^ K *
            ((3 : ℝ) ^ j * (tau₁ - tau₂)) := by
      ring
    rw [hRecDiff, hCompatDiff] at hComb
    push_cast at hComb ⊢
    linear_combination (1 / 4 : ℝ) * hComb
  have hMainZ :
      (3 : ℤ) ^ j * (J₁ - J₂) =
        (2 : ℤ) ^ K * (z₁ - z₂) := by
    exact_mod_cast hMainR
  have hMod :
      (3 : ℤ) ^ j * (J₁ - J₂) ≡
        (3 : ℤ) ^ j * 0 [ZMOD (2 : ℤ) ^ K] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-(z₁ - z₂), ?_⟩
    rw [hMainZ]
    ring
  have hCancel :
      J₁ - J₂ ≡ 0 [ZMOD (2 : ℤ) ^ K] :=
    cancel_threePow_modEq_lattice hMod
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  have hJLo : -((2 : ℤ) ^ K) < J₁ - J₂ := by
    exact_mod_cast hJLoR
  have hJHi : J₁ - J₂ < (2 : ℤ) ^ K := by
    exact_mod_cast hJHiR
  have hPowPos : (0 : ℤ) < (2 : ℤ) ^ K := by positivity
  have hqEq :
      J₁ - J₂ = -((2 : ℤ) ^ K) * q := by
    linear_combination -hq
  have hqZero : q = 0 := by
    by_contra hqNe
    have hCases : q ≤ -1 ∨ 1 ≤ q := by
      omega
    rcases hCases with hqNeg | hqPos
    · have hpNonneg : 0 ≤ (2 : ℤ) ^ K :=
        le_of_lt hPowPos
      have hpq :
          (2 : ℤ) ^ K * q ≤ -((2 : ℤ) ^ K) := by
        calc
          (2 : ℤ) ^ K * q
              ≤ (2 : ℤ) ^ K * (-1) :=
            mul_le_mul_of_nonneg_left hqNeg hpNonneg
          _ = -((2 : ℤ) ^ K) := by ring
      have hdGe :
          (2 : ℤ) ^ K ≤ J₁ - J₂ := by
        rw [hqEq]
        linarith
      exact (not_le_of_gt hJHi) hdGe
    · have hpNonneg : 0 ≤ (2 : ℤ) ^ K :=
        le_of_lt hPowPos
      have hpq :
          (2 : ℤ) ^ K ≤ (2 : ℤ) ^ K * q := by
        calc
          (2 : ℤ) ^ K = (2 : ℤ) ^ K * 1 := by ring
          _ ≤ (2 : ℤ) ^ K * q :=
            mul_le_mul_of_nonneg_left hqPos hpNonneg
      have hdLe :
          J₁ - J₂ ≤ -((2 : ℤ) ^ K) := by
        rw [hqEq]
        linarith
      exact (not_le_of_gt hJLo) hdLe
  have hDiffZero : J₁ - J₂ = 0 := by
    rw [hqZero] at hq
    simpa using hq.symm
  exact sub_eq_zero.mp hDiffZero

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

/--
連続する future-minimum canonical natural completions が与えられたとき、
block 全体の actual-compatible branch digit `J` は存在一意。

branch residue には Stage 5 の既存 affine canonical start をそのまま使う。
-/
theorem exists_unique_nextFutureMinimum_actualCompatible_blockBranchDigit_of_globalCST
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
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent j * u)
    (huPos : 0 < u)
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth j + 1)) :
    ∃! J : ℤ,
      ∃ tauNext : ℝ, ∃ z : ℤ,
        (canonicalStartOfAffineData
              j (infiniteSurvivorDefect O.exponent i + 1)
              (Word.affineConst (O.segmentWord i (j - i))) : ℝ) /
              (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i +
            4 * (J : ℝ) =
          (2 : ℝ) ^
              (Critical.beattyIndex (j - i) +
                Critical.beattyCarry i (j - i)) * tauNext -
            O.normalizedCompletionLiftCoefficient i t ∧
        (0 < tauNext ∧ tauNext < 4) ∧
        O.defectActualResidueFraction j +
            ((3 : ℝ) ^ j / 4) * (tauNext - 2) = (z : ℝ) := by
  rcases
      O.exists_nextFutureMinimum_normalizedCompletionBlockBranchDigit_of_globalCST
        G SInf hi hStart hNext hStartI hStartJ with ⟨J, hBranch, hLift⟩
  have hTauJ :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  rcases
      O.exists_integer_defectActualResidueFraction_add_scaled_centeredLift
        SInf (lt_trans hi hNext.1) hStartJ with ⟨z, hz⟩
  have hCompat :
      O.defectActualResidueFraction j +
          ((3 : ℝ) ^ j / 4) *
            (O.normalizedCompletionLiftCoefficient j u - 2) = (z : ℝ) := by
    simpa [centeredNormalizedCompletionLiftCoefficient] using hz
  have hRec :
      (canonicalStartOfAffineData
            j (infiniteSurvivorDefect O.exponent i + 1)
            (Word.affineConst (O.segmentWord i (j - i))) : ℝ) /
            (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i +
          4 * (J : ℝ) =
        (2 : ℝ) ^
            (Critical.beattyIndex (j - i) +
              Critical.beattyCarry i (j - i)) *
            O.normalizedCompletionLiftCoefficient j u -
          O.normalizedCompletionLiftCoefficient i t := by
    rw [← hBranch]
    exact hLift
  refine ⟨J, ?_, ?_⟩
  · exact
      ⟨O.normalizedCompletionLiftCoefficient j u, z,
        hRec, hTauJ, hCompat⟩
  · intro J' hJ'
    rcases hJ' with ⟨tauNext, z', hRec', hTauNext, hCompat'⟩
    have hEq :=
      Bridge.actualCompatible_normalizedCompletionBlockBranchDigit_unique
        j
        (Critical.beattyIndex (j - i) + Critical.beattyCarry i (j - i))
        (O.normalizedCompletionLiftCoefficient i t)
        ((canonicalStartOfAffineData
            j (infiniteSurvivorDefect O.exponent i + 1)
            (Word.affineConst (O.segmentWord i (j - i))) : ℝ) /
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent i)
        (O.normalizedCompletionLiftCoefficient j u)
        tauNext
        (O.defectActualResidueFraction j)
        J J' z z'
        hRec hRec' hTauJ hTauNext hCompat hCompat'
    exact hEq.symm

end OddOrbit
end Collatz3
