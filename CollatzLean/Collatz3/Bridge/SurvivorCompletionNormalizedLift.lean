import CollatzLean.Collatz3.Bridge.SurvivorCompletionFiveBranch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: completion lift cocycle の defect-normalized 座標

`SurvivorCompletionFiveBranch` では future-minimum `e_m=1` anchor で

`q_m = 2 t_(m+1) - t_m`

が法 `2^(δ_m+2)` の一つの canonical residue class に属し、通常の整数としても
5候補しか持たないことを得た。

このファイルでは defect scale `2^δ_m` で割るだけの薄い実数座標を導入する。

* lift coefficient:

  `tau_m(t) = t / 2^δ_m`

* canonical cocycle residue:

  `rho(m,δ) = completionCocycleResidue(m,δ+1) / 2^δ`

既存 bound `t < 2^(δ+2)` により `tau < 4`、canonical residue も
`0 <= rho < 4` に入る。

従って巨大な modulus `2^(δ+2)` 上の5候補は normalized 座標では exact に

`rho-4, rho, rho+4, rho+8, rho+12`

という fixed spacing の5本になる。

さらに `e_m=1` かつ defect flat なら

`q_m / 2^δ = 2 tau_(m+1) - tau_m < 8`

なので上二本 `rho+8`, `rho+12` は排除され、3候補まで減る。

新しい completion state は作らず、既存 lift coefficient と residue を scale して読むだけである。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
completion natural lift coefficient `t` を current survivor defect scale で正規化した実数値。

`tau_m(t) = t / 2^δ_m`。
-/
noncomputable def normalizedCompletionLiftCoefficient
    (O : Collatz3.OddOrbit)
    (m t : ℕ) : ℝ :=
  (t : ℝ) /
    (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m

/--
completion cocycle の canonical residue を defect scale で正規化した実数値。

`rho(m,δ) = r(m,δ+1) / 2^δ`。
-/
noncomputable def normalizedCompletionCocycleResidue
    (m δ : ℕ) : ℝ :=
  (completionCocycleResidue m (δ + 1) : ℝ) /
    (2 : ℝ) ^ δ

/-- normalized lift coefficient は常に非負。 -/
theorem normalizedCompletionLiftCoefficient_nonneg
    (O : Collatz3.OddOrbit)
    (m t : ℕ) :
    0 ≤ O.normalizedCompletionLiftCoefficient m t := by
  unfold normalizedCompletionLiftCoefficient
  positivity

/--
`0 < t` なら normalized lift coefficient も strict に正。
-/
theorem normalizedCompletionLiftCoefficient_pos
    (O : Collatz3.OddOrbit)
    {m t : ℕ}
    (ht : 0 < t) :
    0 < O.normalizedCompletionLiftCoefficient m t := by
  unfold normalizedCompletionLiftCoefficient
  positivity

/--
既存 completion bound `t < 2^(δ_m+2)` は normalized 座標で `tau_m(t) < 4` になる。
-/
theorem normalizedCompletionLiftCoefficient_lt_four_of_lt
    (O : Collatz3.OddOrbit)
    {m t : ℕ}
    (ht :
      t < 2 ^ (infiniteSurvivorDefect O.exponent m + 2)) :
    O.normalizedCompletionLiftCoefficient m t < 4 := by
  have htR :
      (t : ℝ) <
        (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) := by
    exact_mod_cast ht
  have hPow :
      (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2) =
        4 * (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
    rw [pow_add]
    ring
  unfold normalizedCompletionLiftCoefficient
  apply (div_lt_iff₀
    (by positivity :
      (0 : ℝ) < (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m)).2
  rw [hPow] at htR
  simpa [mul_comm] using htR

/--
canonical normalized residue は常に `[0,4)` に入る。
-/
theorem normalizedCompletionCocycleResidue_mem_Ico_zero_four
    (m δ : ℕ) :
    0 ≤ normalizedCompletionCocycleResidue m δ ∧
      normalizedCompletionCocycleResidue m δ < 4 := by
  constructor
  · unfold normalizedCompletionCocycleResidue
    positivity
  · have hNat := completionCocycleResidue_lt_modulus m (δ + 1)
    have hNat' :
        completionCocycleResidue m (δ + 1) < 2 ^ (δ + 2) := by
      simpa [Nat.add_assoc] using hNat
    have hR :
        (completionCocycleResidue m (δ + 1) : ℝ) <
          (2 : ℝ) ^ (δ + 2) := by
      exact_mod_cast hNat'
    have hPow :
        (2 : ℝ) ^ (δ + 2) = 4 * (2 : ℝ) ^ δ := by
      rw [pow_add]
      ring
    unfold normalizedCompletionCocycleResidue
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ δ)).2
    rw [hPow] at hR
    simpa [mul_comm] using hR

/--
`e_m=1` かつ defect flat のとき normalized lift step は

`q_m / 2^δ = 2 tau_(m+1) - tau_m`。
-/
theorem normalizedCompletionLiftStep_eq_two_mul_sub_of_flat
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (he : O.exponent m = 1)
    (hFlat :
      infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
      2 * O.normalizedCompletionLiftCoefficient (m + 1) u -
        O.normalizedCompletionLiftCoefficient m t := by
  have hq :=
    O.endpointCompletionLiftStep_eq_two_mul_sub_of_exponent_eq_one
      (t := t) (u := u) he
  unfold normalizedCompletionLiftCoefficient
  rw [hFlat, hq]
  push_cast
  field_simp

/--
`e_m=1` かつ defect `+1` のとき normalized lift step は

`q_m / 2^δ = 4 tau_(m+1) - tau_m`。
-/
theorem normalizedCompletionLiftStep_eq_four_mul_sub_of_rise
    (O : Collatz3.OddOrbit)
    {m t u : ℕ}
    (he : O.exponent m = 1)
    (hRise :
      infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m + 1) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
      4 * O.normalizedCompletionLiftCoefficient (m + 1) u -
        O.normalizedCompletionLiftCoefficient m t := by
  have hq :=
    O.endpointCompletionLiftStep_eq_two_mul_sub_of_exponent_eq_one
      (t := t) (u := u) he
  unfold normalizedCompletionLiftCoefficient
  rw [hRise, hq]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/--
`e_m=1` の一歩は normalized completion 座標でも flat / rise の二式に exact に分岐する。
-/
theorem normalizedCompletionLiftStep_flat_or_rise
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (he : O.exponent m = 1) :
    (infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m ∧
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
        2 * O.normalizedCompletionLiftCoefficient (m + 1) u -
          O.normalizedCompletionLiftCoefficient m t) ∨
    (infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m + 1 ∧
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m =
        4 * O.normalizedCompletionLiftCoefficient (m + 1) u -
          O.normalizedCompletionLiftCoefficient m t) := by
  rcases O.infiniteSurvivorDefect_succ_eq_self_or_succ_of_exponent_eq_one
      SInf he with hFlat | hRise
  · exact Or.inl
      ⟨hFlat,
        O.normalizedCompletionLiftStep_eq_two_mul_sub_of_flat he hFlat⟩
  · exact Or.inr
      ⟨hRise,
        O.normalizedCompletionLiftStep_eq_four_mul_sub_of_rise he hRise⟩

/--
future-minimum `e_m=1` completion cocycle の5候補を defect scale で正規化した形。

`δ=δ_m`, `rho=r(m,δ+1)/2^δ` とすると

`q_m/2^δ ∈ {rho-4, rho, rho+4, rho+8, rho+12}`。

候補間隔が defect に依存しない fixed `4` になることが中心。
-/
theorem endpointCompletionLiftStep_normalized_five_candidates_defect_of_exponent_eq_one
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
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let δ := infiniteSurvivorDefect O.exponent m
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ δ
    let rho := normalizedCompletionCocycleResidue m δ
    qn = rho - 4 ∨
      qn = rho ∨
      qn = rho + 4 ∨
      qn = rho + 8 ∨
      qn = rho + 12 := by
  let δ := infiniteSurvivorDefect O.exponent m
  change
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ - 4 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 4 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 8 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 12
  let r : ℕ := completionCocycleResidue m (δ + 1)
  let M : ℤ := (2 : ℤ) ^ (δ + 2)
  have hFive :
      endpointCompletionLiftStep O m t u = (r : ℤ) - M ∨
        endpointCompletionLiftStep O m t u = (r : ℤ) ∨
        endpointCompletionLiftStep O m t u = (r : ℤ) + M ∨
        endpointCompletionLiftStep O m t u = (r : ℤ) + 2 * M ∨
        endpointCompletionLiftStep O m t u = (r : ℤ) + 3 * M := by
    simpa only [δ, r, M] using
      O.endpointCompletionLiftStep_five_candidates_defect_of_exponent_eq_one
        SInf hm he hStartM hStartN ht hu
  have hMReal :
      (M : ℝ) = 4 * (2 : ℝ) ^ δ := by
    dsimp [M]
    push_cast
    rw [pow_add]
    ring
  have hrNorm :
      (r : ℝ) / (2 : ℝ) ^ δ =
        normalizedCompletionCocycleResidue m δ := by
    rfl
  rcases hFive with h | h | h | h | h
  · left
    calc
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ δ
          = ((r : ℝ) - (M : ℝ)) / (2 : ℝ) ^ δ := by
              rw [h]
              push_cast
              rfl
      _ = (r : ℝ) / (2 : ℝ) ^ δ - 4 := by
            rw [hMReal]
            field_simp
      _ = normalizedCompletionCocycleResidue m δ - 4 := by rw [hrNorm]
  · right; left
    calc
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ δ
          = (r : ℝ) / (2 : ℝ) ^ δ := by
              rw [h]
              push_cast
              rfl
      _ = normalizedCompletionCocycleResidue m δ := hrNorm
  · right; right; left
    calc
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ δ
          = ((r : ℝ) + (M : ℝ)) / (2 : ℝ) ^ δ := by
              rw [h]
              push_cast
              rfl
      _ = (r : ℝ) / (2 : ℝ) ^ δ + 4 := by
            rw [hMReal]
            field_simp
      _ = normalizedCompletionCocycleResidue m δ + 4 := by rw [hrNorm]
  · right; right; right; left
    calc
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ δ
          = ((r : ℝ) + 2 * (M : ℝ)) / (2 : ℝ) ^ δ := by
              rw [h]
              push_cast
              rfl
      _ = (r : ℝ) / (2 : ℝ) ^ δ + 8 := by
            rw [hMReal]
            field_simp
            ring
      _ = normalizedCompletionCocycleResidue m δ + 8 := by rw [hrNorm]
  · right; right; right; right
    calc
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
            (2 : ℝ) ^ δ
          = ((r : ℝ) + 3 * (M : ℝ)) / (2 : ℝ) ^ δ := by
              rw [h]
              push_cast
              rfl
      _ = (r : ℝ) / (2 : ℝ) ^ δ + 12 := by
            rw [hMReal]
            field_simp
            ring
      _ = normalizedCompletionCocycleResidue m δ + 12 := by rw [hrNorm]

/--
`e_m=1` かつ defect flat なら normalized lift step は strict に `8` 未満。

`q/2^δ = 2 tau_(m+1)-tau_m` と `tau_(m+1)<4`, `tau_m>=0` を使う。
-/
theorem normalizedCompletionLiftStep_lt_eight_of_flat
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (he : O.exponent m = 1)
    (hFlat :
      infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m)
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m < 8 := by
  have huDef :
      u < 2 ^ (infiniteSurvivorDefect O.exponent (m + 1) + 2) := by
    have hu' := hu
    rw [O.endpointCompletionExtraDepth_eq_defect_add_one SInf (m + 1)] at hu'
    simpa [Nat.add_assoc] using hu'
  have huLt :=
    O.normalizedCompletionLiftCoefficient_lt_four_of_lt
      (m := m + 1) huDef
  have htNonneg := O.normalizedCompletionLiftCoefficient_nonneg m t
  have hEq :=
    O.normalizedCompletionLiftStep_eq_two_mul_sub_of_flat
      (t := t) (u := u) he hFlat
  linarith

/--
flat defect branch では5候補の上二本が消え、normalized cocycle は3候補に縮む。

`q/2^δ ∈ {rho-4, rho, rho+4}`。
-/
theorem endpointCompletionLiftStep_normalized_three_candidates_of_flat
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m t u : ℕ}
    (hm : 0 < m)
    (he : O.exponent m = 1)
    (hFlat :
      infiniteSurvivorDefect O.exponent (m + 1) =
        infiniteSurvivorDefect O.exponent m)
    (hStartM :
      O.endpointCompletionStart SInf hm =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent m * t)
    (hStartN :
      O.endpointCompletionStart SInf (by omega : 0 < m + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (m + 1) * u)
    (ht : t < 2 ^ (O.endpointCompletionExtraDepth m + 1))
    (hu : u < 2 ^ (O.endpointCompletionExtraDepth (m + 1) + 1)) :
    let δ := infiniteSurvivorDefect O.exponent m
    let qn :=
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
        (2 : ℝ) ^ δ
    let rho := normalizedCompletionCocycleResidue m δ
    qn = rho - 4 ∨
      qn = rho ∨
      qn = rho + 4 := by
  let δ := infiniteSurvivorDefect O.exponent m
  change
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ - 4 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 4
  have hFive :=
    O.endpointCompletionLiftStep_normalized_five_candidates_defect_of_exponent_eq_one
      SInf hm he hStartM hStartN ht hu
  change
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ - 4 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 4 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 8 ∨
      ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
          (2 : ℝ) ^ δ = normalizedCompletionCocycleResidue m δ + 12 at hFive
  have hLt :=
    O.normalizedCompletionLiftStep_lt_eight_of_flat
      SInf (t := t) he hFlat hu
  change
    ((endpointCompletionLiftStep O m t u : ℤ) : ℝ) /
      (2 : ℝ) ^ δ < 8 at hLt
  have hRho :=
    normalizedCompletionCocycleResidue_mem_Ico_zero_four m δ
  rcases hFive with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    rw [h] at hLt
    linarith [hRho.1]
  · exfalso
    rw [h] at hLt
    linarith [hRho.1]

end OddOrbit
end Collatz3
