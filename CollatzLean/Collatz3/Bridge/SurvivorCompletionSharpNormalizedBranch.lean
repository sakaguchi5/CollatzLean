import CollatzLean.Collatz3.Bridge.SurvivorCompletionAllStepNormalizedLift
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: normalized completion branch の全-step sharp 分類

actual completion lift が連続幅 `m,m+1` で存在するとき、既存 exact residue theorem から

`q_m / 2^δ_m = rho_m + 4 j`

となる整数 branch digit `j` が存在する。

一方、全-step recurrence は

`q_m / 2^δ_m = 2^(1+s_m) tau_(m+1) - tau_m`

であり、natural lift bound から両 `tau` は `(0,4)` に入る。
従って

* `s_m=0` ではまず3候補、さらに `tau_m+rho_m` で最大2候補、
* `s_m=1` ではまず5候補、さらに `tau_m+rho_m` で最大4候補

まで削れる。

この結果には `e_m=1` を仮定しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- current / next natural lift bound を normalized `(0,4)` bound へ移す。 -/
theorem normalizedCompletionLiftCoefficient_bounds_of_completionBound
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t : ℕ}
    (htPos : 0 < t)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1)) :
    0 < O.normalizedCompletionLiftCoefficient m t ∧
      O.normalizedCompletionLiftCoefficient m t < 4 := by
  have htDef :
      t < 2 ^ (infiniteSurvivorDefect O.exponent m + 2) := by
    have h := ht
    rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf m] at h
    simpa [Nat.add_assoc] using h
  exact
    ⟨O.normalizedCompletionLiftCoefficient_pos htPos,
      O.normalizedCompletionLiftCoefficient_lt_four_of_lt htDef⟩

/--
actual lift step は normalized canonical residue から `4ℤ` だけずれる。

`q/2^δ = rho + 4j`。
-/
theorem exists_normalizedCompletionLiftStep_residue_digit
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
    ∃ j : ℤ,
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
        normalizedCompletionCocycleResidue
          m (infiniteSurvivorDefect O.exponent m) + 4 * (j : ℝ) := by
  let δ := infiniteSurvivorDefect O.exponent m
  let q : ℤ := endpointCompletionLiftStep O m t u
  let r : ℤ := completionCocycleResidue m (δ + 1)
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  have hMod :=
    O.endpointCompletionLiftStep_modEq_completionCocycleResidue_defect
      SInf hm hStartM hStartN
  have hMod' : q ≡ r [ZMOD M] := by
    simpa [q, r, M, δ] using hMod
  rcases Int.modEq_iff_add_fac.mp hMod' with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  have hk' : q = r + M * (-k) := by
    rw [hk]
    ring
  have hkR := congrArg (fun z : ℤ => (z : ℝ)) hk'
  push_cast at hkR
  have hM : (M : ℝ) = 4 * (2 : ℝ) ^ δ := by
    dsimp [M]
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [hM] at hkR
  unfold normalizedCompletionCocycleResidue
  dsimp [q, r, δ] at hkR ⊢
  field_simp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hkR

/-- `s_m=0` なら normalized lift step は3候補に入る。 -/
theorem normalizedCompletionLiftStep_three_candidates_of_sturmianStep_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hs : survivorSturmianStep m = 0)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (htPos : 0 < t)
    (huPos : 0 < u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m
    let rho :=
      normalizedCompletionCocycleResidue m (infiniteSurvivorDefect O.exponent m)
    qn = rho - 4 ∨ qn = rho ∨ qn = rho + 4 := by
  dsimp
  rcases O.exists_normalizedCompletionLiftStep_residue_digit
      SInf hm hStartM hStartN with ⟨j, hj⟩
  have hTauM :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf htPos ht
  have hTauN :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  have hRec :=
    O.normalizedCompletionLiftStep_eq_two_mul_sub_of_sturmianStep_zero
      SInf (t := t) (u := u) hs
  have hRho :=
    normalizedCompletionCocycleResidue_mem_Ico_zero_four
      m (infiniteSurvivorDefect O.exponent m)
  have hjLoR : (-2 : ℝ) < (j : ℝ) := by
    rw [hj] at hRec
    nlinarith [hTauM.1, hTauM.2, hTauN.1, hTauN.2, hRho.1, hRho.2]
  have hjHiR : (j : ℝ) < 2 := by
    rw [hj] at hRec
    nlinarith [hTauM.1, hTauM.2, hTauN.1, hTauN.2, hRho.1, hRho.2]
  have hjLo : (-2 : ℤ) < j := by exact_mod_cast hjLoR
  have hjHi : j < 2 := by exact_mod_cast hjHiR
  have hjCases : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hjCases with rfl | rfl | rfl
  · left; norm_num at hj ⊢; linarith
  · right; left; norm_num at hj ⊢; linarith
  · right; right; norm_num at hj ⊢; linarith

/-- `s_m=1` なら normalized lift step は5候補に入る。 -/
theorem normalizedCompletionLiftStep_five_candidates_of_sturmianStep_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hs : survivorSturmianStep m = 1)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (htPos : 0 < t)
    (huPos : 0 < u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m
    let rho :=
      normalizedCompletionCocycleResidue m (infiniteSurvivorDefect O.exponent m)
    qn = rho - 4 ∨ qn = rho ∨ qn = rho + 4 ∨
      qn = rho + 8 ∨ qn = rho + 12 := by
  dsimp
  rcases O.exists_normalizedCompletionLiftStep_residue_digit
      SInf hm hStartM hStartN with ⟨j, hj⟩
  have hTauM :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf htPos ht
  have hTauN :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  have hRec :=
    O.normalizedCompletionLiftStep_eq_four_mul_sub_of_sturmianStep_one
      SInf (t := t) (u := u) hs
  have hRho :=
    normalizedCompletionCocycleResidue_mem_Ico_zero_four
      m (infiniteSurvivorDefect O.exponent m)
  have hjLoR : (-2 : ℝ) < (j : ℝ) := by
    rw [hj] at hRec
    nlinarith [hTauM.1, hTauM.2, hTauN.1, hTauN.2, hRho.1, hRho.2]
  have hjHiR : (j : ℝ) < 4 := by
    rw [hj] at hRec
    nlinarith [hTauM.1, hTauM.2, hTauN.1, hTauN.2, hRho.1, hRho.2]
  have hjLo : (-2 : ℤ) < j := by exact_mod_cast hjLoR
  have hjHi : j < 4 := by exact_mod_cast hjHiR
  have hjCases : j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hjCases with rfl | rfl | rfl | rfl | rfl
  · left; norm_num at hj ⊢; linarith
  · right; left; norm_num at hj ⊢; linarith
  · right; right; left; norm_num at hj ⊢; linarith
  · right; right; right; left; norm_num at hj ⊢; linarith
  · right; right; right; right; norm_num at hj ⊢; linarith

/--
`s_m=0` の3候補は `A=tau_m+rho_m` の位置で最大2候補まで落ちる。
境界 `A=4` では中央1候補だけになる。
-/
theorem normalizedCompletionLiftStep_sharp_candidates_of_sturmianStep_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hs : survivorSturmianStep m = 0)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (htPos : 0 < t)
    (huPos : 0 < u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m
    let tau := O.normalizedCompletionLiftCoefficient m t
    let rho :=
      normalizedCompletionCocycleResidue m (infiniteSurvivorDefect O.exponent m)
    (tau + rho < 4 → qn = rho ∨ qn = rho + 4) ∧
    (tau + rho = 4 → qn = rho) ∧
    (4 < tau + rho → qn = rho - 4 ∨ qn = rho) := by
  dsimp
  have hThree :=
    O.normalizedCompletionLiftStep_three_candidates_of_sturmianStep_zero
      SInf hm hs hStartM hStartN htPos huPos ht hu
  have hTauN :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  have hRec :=
    O.normalizedCompletionLiftStep_eq_two_mul_sub_of_sturmianStep_zero
      SInf (t := t) (u := u) hs
  constructor
  · intro hA
    rcases hThree with h | h | h
    · exfalso; rw [h] at hRec; linarith [hTauN.1]
    · exact Or.inl h
    · exact Or.inr h
  · constructor
    · intro hA
      rcases hThree with h | h | h
      · exfalso; rw [h] at hRec; linarith [hTauN.1]
      · exact h
      · exfalso; rw [h] at hRec; linarith [hTauN.2]
    · intro hA
      rcases hThree with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; rw [h] at hRec; linarith [hTauN.2]

/--
`s_m=1` の5候補は `A=tau_m+rho_m` の位置で最大4候補まで落ちる。
境界 `A=4` では中央3候補だけになる。
-/
theorem normalizedCompletionLiftStep_sharp_candidates_of_sturmianStep_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (hs : survivorSturmianStep m = 1)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (htPos : 0 < t)
    (huPos : 0 < u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m
    let tau := O.normalizedCompletionLiftCoefficient m t
    let rho :=
      normalizedCompletionCocycleResidue m (infiniteSurvivorDefect O.exponent m)
    (tau + rho < 4 →
      qn = rho ∨ qn = rho + 4 ∨ qn = rho + 8 ∨ qn = rho + 12) ∧
    (tau + rho = 4 →
      qn = rho ∨ qn = rho + 4 ∨ qn = rho + 8) ∧
    (4 < tau + rho →
      qn = rho - 4 ∨ qn = rho ∨ qn = rho + 4 ∨ qn = rho + 8) := by
  dsimp
  have hFive :=
    O.normalizedCompletionLiftStep_five_candidates_of_sturmianStep_one
      SInf hm hs hStartM hStartN htPos huPos ht hu
  have hTauN :=
    O.normalizedCompletionLiftCoefficient_bounds_of_completionBound
      SInf huPos hu
  have hRec :=
    O.normalizedCompletionLiftStep_eq_four_mul_sub_of_sturmianStep_one
      SInf (t := t) (u := u) hs
  constructor
  · intro hA
    rcases hFive with h | h | h | h | h
    · exfalso; rw [h] at hRec; linarith [hTauN.1]
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · constructor
    · intro hA
      rcases hFive with h | h | h | h | h
      · exfalso; rw [h] at hRec; linarith [hTauN.1]
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso; rw [h] at hRec; linarith [hTauN.2]
    · intro hA
      rcases hFive with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exfalso; rw [h] at hRec; linarith [hTauN.2]

end OddOrbit
end Collatz3
