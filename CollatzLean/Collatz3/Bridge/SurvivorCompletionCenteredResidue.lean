import CollatzLean.Collatz3.Bridge.SurvivorCompletionResidueDynamics
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: completion residue の centered 座標

canonical residue `r(m,δ+1)` は `[0,2^(δ+2))` の代表である。
その midpoint `2^(δ+1)` を引いた

`c(m,δ) = r(m,δ+1) - 2^(δ+1)`

を centered residue とする。正規化後は

`sigma(m,δ) = rho(m,δ) - 2`。

この座標では defining congruence が

`3^(m+1) c(m,δ) ≡ -1 (mod 2^(δ+2))`

へ単純化する。従って future-minimum `e=1` の flat/rise は統一的に

`3 * 2^s * sigma' = sigma + 4 h`, `s∈{0,1}`

と読める。
-/

namespace Collatz3
namespace Bridge

/-- canonical completion cocycle residue を modulus midpoint のまわりへ中心化した整数。 -/
def centeredCompletionCocycleResidue
    (m δ : ℕ) : ℤ :=
  (completionCocycleResidue m (δ + 1) : ℤ) -
    (2 : ℤ) ^ (δ + 1)

/-- centered residue は `-2^(δ+1)` 以上。 -/
theorem neg_twoPow_le_centeredCompletionCocycleResidue
    (m δ : ℕ) :
    -((2 : ℤ) ^ (δ + 1)) ≤ centeredCompletionCocycleResidue m δ := by
  unfold centeredCompletionCocycleResidue
  have h : 0 ≤ (completionCocycleResidue m (δ + 1) : ℤ) := by positivity
  linarith

/-- centered residue は `2^(δ+1)` 未満。 -/
theorem centeredCompletionCocycleResidue_lt_twoPow
    (m δ : ℕ) :
    centeredCompletionCocycleResidue m δ < (2 : ℤ) ^ (δ + 1) := by
  have h := completionCocycleResidue_lt_modulus m (δ + 1)
  have hZ :
      (completionCocycleResidue m (δ + 1) : ℤ) <
        (2 : ℤ) ^ (δ + 2) := by
    exact_mod_cast h
  unfold centeredCompletionCocycleResidue
  rw [show δ + 2 = (δ + 1) + 1 by omega, pow_succ] at hZ
  linarith

/--
centered residue の defining congruence。

`3^(m+1) c ≡ -1 (mod 2^(δ+2))`。
-/
theorem centeredCompletionCocycleResidue_spec
    (m δ : ℕ) :
    (3 : ℤ) ^ (m + 1) * centeredCompletionCocycleResidue m δ ≡
      -1 [ZMOD (2 : ℤ) ^ (δ + 2)] := by
  let A : ℤ := (3 : ℤ) ^ (m + 1)
  let half : ℤ := (2 : ℤ) ^ (δ + 1)
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  let r : ℤ := completionCocycleResidue m (δ + 1)
  have hSpec := completionCocycleResidue_spec_intModEq m (δ + 1)
  rcases threePow_odd_nat (m + 1) with ⟨q, hq⟩
  have hA : A = 2 * (q : ℤ) + 1 := by
    dsimp [A]
    exact_mod_cast hq
  have hHalf : A * half ≡ half [ZMOD M] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨-(q : ℤ), ?_⟩
    dsimp [M, half]
    rw [hA]
    rw [show δ + 2 = (δ + 1) + 1 by omega, pow_succ]
    ring
  have hSpec' : A * r + 1 ≡ half [ZMOD M] := by
    simpa [A, r, half, M, Nat.add_assoc] using hSpec
  have hSub := hSpec'.sub hHalf
  have hMain :
      A * (r - half) + 1 ≡ 0 [ZMOD M] := by
    convert hSub using 1 <;> ring
  have hMinusOne : A * (r - half) ≡ -1 [ZMOD M] := by
    have hAdd :
        A * (r - half) + 1 ≡ (-1 : ℤ) + 1 [ZMOD M] := by
      simpa using hMain
    exact Int.ModEq.add_right_cancel' 1 hAdd
  simpa [centeredCompletionCocycleResidue, A, r, half, M] using hMinusOne

end Bridge

namespace OddOrbit

open Bridge

/-- normalized canonical residue を midpoint `2` のまわりへ中心化する。 -/
noncomputable def centeredNormalizedCompletionCocycleResidue
    (m δ : ℕ) : ℝ :=
  normalizedCompletionCocycleResidue m δ - 2

/-- centered normalized residue は `[-2,2)` に入る。 -/
theorem centeredNormalizedCompletionCocycleResidue_mem_Ico
    (m δ : ℕ) :
    -2 ≤ centeredNormalizedCompletionCocycleResidue m δ ∧
      centeredNormalizedCompletionCocycleResidue m δ < 2 := by
  have h := normalizedCompletionCocycleResidue_mem_Ico_zero_four m δ
  unfold centeredNormalizedCompletionCocycleResidue
  constructor <;> linarith

/-- centered normalized residue は integer centered residue を `2^δ` で割ったもの。 -/
theorem centeredNormalizedCompletionCocycleResidue_eq_centered_div
    (m δ : ℕ) :
    centeredNormalizedCompletionCocycleResidue m δ =
      (centeredCompletionCocycleResidue m δ : ℝ) / (2 : ℝ) ^ δ := by
  unfold centeredNormalizedCompletionCocycleResidue
    normalizedCompletionCocycleResidue centeredCompletionCocycleResidue
  push_cast
  rw [pow_succ]
  field_simp

/-- flat 時の centered normalized residue transition。 -/
theorem exists_centeredNormalizedCompletionCocycleResidue_flat_transition_digit
    (m δ : ℕ) :
    ∃ h : ℤ,
      3 * centeredNormalizedCompletionCocycleResidue (m + 1) δ =
        centeredNormalizedCompletionCocycleResidue m δ + 4 * (h : ℝ) := by
  rcases exists_normalizedCompletionCocycleResidue_flat_transition_digit m δ with
    ⟨k, hk⟩
  refine ⟨k - 1, ?_⟩
  unfold centeredNormalizedCompletionCocycleResidue
  push_cast
  linarith

/-- rise 時の centered normalized residue transition。 -/
theorem exists_centeredNormalizedCompletionCocycleResidue_rise_transition_digit
    (m δ : ℕ) :
    ∃ h : ℤ,
      6 * centeredNormalizedCompletionCocycleResidue (m + 1) (δ + 1) =
        centeredNormalizedCompletionCocycleResidue m δ + 4 * (h : ℝ) := by
  rcases exists_normalizedCompletionCocycleResidue_rise_transition_digit m δ with
    ⟨k, hk⟩
  refine ⟨k - 2, ?_⟩
  unfold centeredNormalizedCompletionCocycleResidue
  push_cast
  linarith

/--
`survivorSturmianStep m = s` (`s=0/1`) を使った centered residue の統一形。
`e_m=1` なら next defect は `δ+s` なので、flat/rise の二式を一つにまとめられる。
-/
theorem exists_centeredNormalizedCompletionCocycleResidue_transition_digit_of_exponent_eq_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (he : O.exponent m = 1) :
    ∃ h : ℤ,
      3 * (2 : ℝ) ^ survivorSturmianStep m *
          centeredNormalizedCompletionCocycleResidue
            (m + 1) (infiniteSurvivorDefect O.exponent (m + 1)) =
        centeredNormalizedCompletionCocycleResidue
            m (infiniteSurvivorDefect O.exponent m) +
          4 * (h : ℝ) := by
  have hDef := O.infiniteSurvivorDefect_succ_of_exponent_eq_one SInf he
  rcases survivorSturmianStep_eq_zero_or_one m with hs | hs
  · rw [hs] at hDef
    have hFlat :=
      exists_centeredNormalizedCompletionCocycleResidue_flat_transition_digit
        m (infiniteSurvivorDefect O.exponent m)
    rcases hFlat with ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hs, hDef]
    norm_num
    exact hh
  · rw [hs] at hDef
    have hRise :=
      exists_centeredNormalizedCompletionCocycleResidue_rise_transition_digit
        m (infiniteSurvivorDefect O.exponent m)
    rcases hRise with ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hs, hDef]
    norm_num
    exact hh

end OddOrbit
end Collatz3
