import CollatzLean.Collatz3.Experimental.RationalScaledSlopeBridge
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.NumberTheory.Real.Irrational

/-!
# Collatz3 experimental: 非無理 slope から自然数比を抽出する

canonical slope の rational 側で、これまでは

`residualSlope β = p / q`

という自然数 `p,q` を外から与えていた。

このファイルではその最後の外部入力を除く。

まず一般の実数 `ρ` について

* `ρ` が無理数でない
* `0 ≤ ρ`

だけから

`ρ = p / q`, `p q : ℕ`, `0 < q`

を導く。

さらに `ρ ≤ 1` があれば `p ≤ q` も導く。

中心 theorem は roof / carry に依存しない純粋な有理数抽出であり、
`HasUnitCarry` は canonical `residualSlope β` に適用する corollary 側だけで使う。
-/

namespace Collatz3
namespace Experimental

/--
非無理な非負実数は、正の自然数分母を持つ自然数比で表せる。

`¬ Irrational ρ` と `0 ≤ ρ` だけが必要で、unit-carry roof には依存しない。
-/
theorem exists_nat_ratio_of_not_irrational_nonneg
    {ρ : ℝ}
    (hNotIrr : ¬ Irrational ρ)
    (hNonneg : 0 ≤ ρ) :
    ∃ p q : ℕ,
      0 < q ∧
        ρ = (p : ℝ) / (q : ℝ) := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hNotIrr
  have hrNonnegReal : (0 : ℝ) ≤ (r : ℝ) := by
    rw [← hr]
    exact hNonneg
  have hrNonnegRat : (0 : ℚ) ≤ r := by
    exact_mod_cast hrNonnegReal
  let s : ℚ≥0 := ⟨r, hrNonnegRat⟩
  refine ⟨s.num, s.den, s.den_pos, ?_⟩
  calc
    ρ = (r : ℝ) := hr
    _ = (s : ℝ) := by
      symm
      simp only [NNRat.cast_mk, s]
    _ = (s.num : ℝ) / (s.den : ℝ) := by
      rw [NNRat.cast_def]

/--
さらに `ρ ≤ 1` なら、自然数比は `p ≤ q` として取れる。

canonical residual slope は既に `[0,1]` に入るため、
rational case では分子も自動的に分母以下になる。
-/
theorem exists_nat_ratio_of_not_irrational_unitInterval
    {ρ : ℝ}
    (hNotIrr : ¬ Irrational ρ)
    (hBounds : 0 ≤ ρ ∧ ρ ≤ 1) :
    ∃ p q : ℕ,
      0 < q ∧
        p ≤ q ∧
          ρ = (p : ℝ) / (q : ℝ) := by
  obtain ⟨p, q, hq, hSlope⟩ :=
    exists_nat_ratio_of_not_irrational_nonneg
      hNotIrr hBounds.1
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hDiv : (p : ℝ) / (q : ℝ) ≤ 1 := by
    rw [← hSlope]
    exact hBounds.2
  have hpqR : (p : ℝ) ≤ (q : ℝ) := by
    have h := (div_le_iff₀ hqR).mp hDiv
    simpa using h
  have hpq : p ≤ q := by
    exact_mod_cast hpqR
  exact ⟨p, q, hq, hpq, hSlope⟩

namespace HasUnitCarry

/--
canonical residual slope は、無理数であるか、
`0 < q`, `p ≤ q` を満たす自然数比 `p/q` であるかのどちらか。

ここで `p,q` は外部入力ではなく `residualSlope β` 自身から得られる。
-/
theorem residualSlope_irrational_or_exists_natRatio
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    Irrational (residualSlope β) ∨
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) := by
  classical
  by_cases hIrr : Irrational (residualSlope β)
  · exact Or.inl hIrr
  · right
    exact exists_nat_ratio_of_not_irrational_unitInterval
      hIrr U.residualSlope_mem_unitInterval

/--
canonical slope が rational 側なら、自然数 `p,q` を外から与えなくても
整数演算版 `IsScaledRationalSlope` まで自動的に得られる。
-/
theorem exists_scaledRationalSlope_of_not_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hNotIrr : ¬ Irrational (residualSlope β)) :
    ∃ p q : ℕ,
      0 < q ∧
        p ≤ q ∧
          residualSlope β =
            (p : ℝ) / (q : ℝ) ∧
            IsScaledRationalSlope β p q := by
  obtain ⟨p, q, hq, hpq, hSlope⟩ :=
    exists_nat_ratio_of_not_irrational_unitInterval
      hNotIrr U.residualSlope_mem_unitInterval
  refine ⟨p, q, hq, hpq, hSlope, ?_⟩
  exact U.residualSlope_scaledRational_of_eq_div hq hSlope

end HasUnitCarry
end Experimental
end Collatz3
