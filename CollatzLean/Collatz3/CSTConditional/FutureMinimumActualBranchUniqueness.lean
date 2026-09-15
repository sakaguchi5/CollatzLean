import CollatzLean.Collatz3.CSTConditional.FutureMinimumActualBranchSelection
import Mathlib.Tactic.LinearCombination

/-!
# Collatz3 CSTConditional: actual-compatible completion branch の一意性

既存の branch separation は、normalized lift-step が `4` だけ離れた
隣接二候補を排除する形だった。

ここでは新しい branch 型や compatibility predicate を導入せず、既存の scalar 条件

* normalized branch: `rho + 4 j`,
* next natural lift bound: `0 < tau' < 4`,
* actual finite compatibility:
  `theta' + (3^(m+1)/4) (tau' - 2) ∈ Z`

だけから、整数 branch digit `j` そのものが一意であることを導く。

`survivorSturmianStep m = 0` では

`tau₁ - tau₂ = 2 (j₁-j₂)`

となり、actual compatibility から `2 ∣ (j₁-j₂)`、
一方 `(0,4)` bound から `|j₁-j₂| < 2` なので差は `0`。

`survivorSturmianStep m = 1` では

`tau₁ - tau₂ = j₁-j₂`

となり、actual compatibility から `4 ∣ (j₁-j₂)`、
一方 `(0,4)` bound から `|j₁-j₂| < 4` なので差は `0`。

したがって actual-compatible normalized completion branch は、
Sturmian step `0/1` のどちらでも高々一つである。
-/

namespace Collatz3
namespace Bridge

/--
Sturmian step `0` の場合、actual-compatible normalized branch digit は一意。

新しい branch object は作らず、二つの候補 `j₁,j₂` が同じ current state と
actual residue に両立すると仮定して直接 `j₁=j₂` を示す。
-/
theorem actualCompatible_normalizedCompletionBranchDigit_unique_of_step_zero
    (m : ℕ)
    (tauCurrent rho theta tau₁ tau₂ : ℝ)
    (j₁ j₂ z₁ z₂ : ℤ)
    (hRec₁ :
      rho + 4 * (j₁ : ℝ) = 2 * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (j₂ : ℝ) = 2 * tau₂ - tauCurrent)
    (hTau₁ : 0 < tau₁ ∧ tau₁ < 4)
    (hTau₂ : 0 < tau₂ ∧ tau₂ < 4)
    (hCompat₁ :
      theta + ((3 : ℝ) ^ (m + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ))
    (hCompat₂ :
      theta + ((3 : ℝ) ^ (m + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ)) :
    j₁ = j₂ := by
  have hTauDiff :
      tau₁ - tau₂ = 2 * (((j₁ - j₂ : ℤ) : ℝ)) := by
    push_cast
    linarith [hRec₁, hRec₂]
  have hDiffLo : (-4 : ℝ) < tau₁ - tau₂ := by
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hDiffHi : tau₁ - tau₂ < 4 := by
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hjLoR : (-2 : ℝ) < (((j₁ - j₂ : ℤ) : ℝ)) := by
    nlinarith [hTauDiff, hDiffLo]
  have hjHiR : (((j₁ - j₂ : ℤ) : ℝ)) < 2 := by
    nlinarith [hTauDiff, hDiffHi]
  have hCompatDiff :
      (3 : ℝ) ^ (m + 1) * (tau₁ - tau₂) =
        4 * ((z₁ : ℝ) - (z₂ : ℝ)) := by
    linear_combination 4 * hCompat₁ - 4 * hCompat₂
  rw [hTauDiff] at hCompatDiff
  have hEqZFull :
      (3 : ℤ) ^ (m + 1) * (2 * (j₁ - j₂)) =
        4 * (z₁ - z₂) := by
    exact_mod_cast hCompatDiff
  have hEqZ :
      (3 : ℤ) ^ (m + 1) * (j₁ - j₂) =
        2 * (z₁ - z₂) := by
    nlinarith [hEqZFull]
  have hMod :
      (3 : ℤ) ^ (m + 1) * (j₁ - j₂) ≡
        (3 : ℤ) ^ (m + 1) * 0
        [ZMOD (2 : ℤ) ^ 1] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-(z₁ - z₂), ?_⟩
    rw [hEqZ]
    norm_num
    ring
  have hCancel :
      j₁ - j₂ ≡ 0 [ZMOD (2 : ℤ) ^ 1] :=
    cancel_threePow_modEq_lattice hMod
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  have hjLo : (-2 : ℤ) < j₁ - j₂ := by
    exact_mod_cast hjLoR
  have hjHi : j₁ - j₂ < 2 := by
    exact_mod_cast hjHiR
  norm_num at hq
  omega

/--
Sturmian step `1` の場合、actual-compatible normalized branch digit は一意。

この場合 branch digit の差がそのまま next normalized lift の差になり、
finite actual compatibility が差を `4ℤ` に強制する。
-/
theorem actualCompatible_normalizedCompletionBranchDigit_unique_of_step_one
    (m : ℕ)
    (tauCurrent rho theta tau₁ tau₂ : ℝ)
    (j₁ j₂ z₁ z₂ : ℤ)
    (hRec₁ :
      rho + 4 * (j₁ : ℝ) = 4 * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (j₂ : ℝ) = 4 * tau₂ - tauCurrent)
    (hTau₁ : 0 < tau₁ ∧ tau₁ < 4)
    (hTau₂ : 0 < tau₂ ∧ tau₂ < 4)
    (hCompat₁ :
      theta + ((3 : ℝ) ^ (m + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ))
    (hCompat₂ :
      theta + ((3 : ℝ) ^ (m + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ)) :
    j₁ = j₂ := by
  have hTauDiff :
      tau₁ - tau₂ = (((j₁ - j₂ : ℤ) : ℝ)) := by
    push_cast
    linarith [hRec₁, hRec₂]
  have hjLoR : (-4 : ℝ) < (((j₁ - j₂ : ℤ) : ℝ)) := by
    rw [← hTauDiff]
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hjHiR : (((j₁ - j₂ : ℤ) : ℝ)) < 4 := by
    rw [← hTauDiff]
    linarith [hTau₁.1, hTau₁.2, hTau₂.1, hTau₂.2]
  have hCompatDiff :
      (3 : ℝ) ^ (m + 1) * (tau₁ - tau₂) =
        4 * ((z₁ : ℝ) - (z₂ : ℝ)) := by
    linear_combination 4 * hCompat₁ - 4 * hCompat₂
  rw [hTauDiff] at hCompatDiff
  have hEqZ :
      (3 : ℤ) ^ (m + 1) * (j₁ - j₂) =
        4 * (z₁ - z₂) := by
    exact_mod_cast hCompatDiff
  have hMod :
      (3 : ℤ) ^ (m + 1) * (j₁ - j₂) ≡
        (3 : ℤ) ^ (m + 1) * 0
        [ZMOD (2 : ℤ) ^ 2] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-(z₁ - z₂), ?_⟩
    rw [hEqZ]
    norm_num
    ring
  have hCancel :
      j₁ - j₂ ≡ 0 [ZMOD (2 : ℤ) ^ 2] :=
    cancel_threePow_modEq_lattice hMod
  rcases Int.modEq_iff_add_fac.mp hCancel with ⟨q, hq⟩
  have hjLo : (-4 : ℤ) < j₁ - j₂ := by
    exact_mod_cast hjLoR
  have hjHi : j₁ - j₂ < 4 := by
    exact_mod_cast hjHiR
  norm_num at hq
  omega

end Bridge

namespace OddOrbit

open Bridge

/--
Sturmian step を場合分けせずに使える branch digit 一意性。

`survivorSturmianStep m` は常に `0` または `1` なので、
既存 normalized recurrence と同じ係数 `2^(1+s_m)` をそのまま仮定に使う。
-/
theorem actualCompatible_normalizedCompletionBranchDigit_unique
    (O : Collatz3.OddOrbit)
    {m : ℕ}
    (tauCurrent rho tau₁ tau₂ : ℝ)
    (j₁ j₂ z₁ z₂ : ℤ)
    (hRec₁ :
      rho + 4 * (j₁ : ℝ) =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₁ - tauCurrent)
    (hRec₂ :
      rho + 4 * (j₂ : ℝ) =
        (2 : ℝ) ^ (1 + survivorSturmianStep m) * tau₂ - tauCurrent)
    (hTau₁ : 0 < tau₁ ∧ tau₁ < 4)
    (hTau₂ : 0 < tau₂ ∧ tau₂ < 4)
    (hCompat₁ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₁ - 2) = (z₁ : ℝ))
    (hCompat₂ :
      O.defectActualResidueFraction (m + 1) +
          ((3 : ℝ) ^ (m + 1) / 4) * (tau₂ - 2) = (z₂ : ℝ)) :
    j₁ = j₂ := by
  rcases survivorSturmianStep_eq_zero_or_one m with hs | hs
  · rw [hs] at hRec₁ hRec₂
    norm_num at hRec₁ hRec₂
    exact
      Bridge.actualCompatible_normalizedCompletionBranchDigit_unique_of_step_zero
        m tauCurrent rho (O.defectActualResidueFraction (m + 1))
        tau₁ tau₂ j₁ j₂ z₁ z₂
        hRec₁ hRec₂ hTau₁ hTau₂ hCompat₁ hCompat₂
  · rw [hs] at hRec₁ hRec₂
    norm_num at hRec₁ hRec₂
    exact
      Bridge.actualCompatible_normalizedCompletionBranchDigit_unique_of_step_one
        m tauCurrent rho (O.defectActualResidueFraction (m + 1))
        tau₁ tau₂ j₁ j₂ z₁ z₂
        hRec₁ hRec₂ hTau₁ hTau₂ hCompat₁ hCompat₂

end OddOrbit
end Collatz3
