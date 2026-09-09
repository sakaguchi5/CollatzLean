import CollatzLean.Collatz3.Experimental.UnitCarryCompleteClassification
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Collatz3 experimental: 有理 slope の既約自然数表示

前段では、canonical slope が有理数のとき

`ρ = p / q`, `0 < q`, `p ≤ q`

という自然数表示を得た。

このファイルでは、`NNRat` が内部ですでに持っている既約性を theorem の出力へ戻す。
新しい仮定を追加するのではなく、

`Nat.Coprime p q`

も slope から導かれる witness の一部として露出させる。

これにより、後段では

`q ∣ n * p  ↔  q ∣ n`

を使って「rational boundary は exactly `q` の倍数」という形へ進める。
-/

namespace Collatz3
namespace Experimental

/--
非無理な非負実数は、互いに素な自然数 `p,q` を用いて
正分母の比 `p/q` として表せる。

roof / carry は使わない純粋な有理数表示定理。
-/
theorem exists_reduced_nat_ratio_of_not_irrational_nonneg
    {ρ : ℝ}
    (hNotIrr : ¬ Irrational ρ)
    (hNonneg : 0 ≤ ρ) :
    ∃ p q : ℕ,
      0 < q ∧
        Nat.Coprime p q ∧
          ρ = (p : ℝ) / (q : ℝ) := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hNotIrr
  have hrNonnegReal : (0 : ℝ) ≤ (r : ℝ) := by
    rw [← hr]
    exact hNonneg
  have hrNonnegRat : (0 : ℚ) ≤ r := by
    exact_mod_cast hrNonnegReal
  let s : ℚ≥0 := ⟨r, hrNonnegRat⟩
  refine ⟨s.num, s.den, s.den_pos, s.coprime_num_den, ?_⟩
  calc
    ρ = (r : ℝ) := hr
    _ = (s : ℝ) := by
      symm
      simp only [NNRat.cast_mk, s]
    _ = (s.num : ℝ) / (s.den : ℝ) := by
      rw [NNRat.cast_def]

/--
さらに `ρ ≤ 1` なら、既約表示を `p ≤ q` として取れる。

したがって `[0,1]` にある rational slope は
`0 < q`, `p ≤ q`, `Coprime p q` を同時に満たす witness を持つ。
-/
theorem exists_reduced_nat_ratio_of_not_irrational_unitInterval
    {ρ : ℝ}
    (hNotIrr : ¬ Irrational ρ)
    (hBounds : 0 ≤ ρ ∧ ρ ≤ 1) :
    ∃ p q : ℕ,
      0 < q ∧
        p ≤ q ∧
          Nat.Coprime p q ∧
            ρ = (p : ℝ) / (q : ℝ) := by
  obtain ⟨p, q, hq, hCoprime, hSlope⟩ :=
    exists_reduced_nat_ratio_of_not_irrational_nonneg
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
  exact ⟨p, q, hq, hpq, hCoprime, hSlope⟩

/--
`p,q` が互いに素なら、`q ∣ n*p` は `q ∣ n` と同値。

後段で rational boundary の位置を `q` の倍数へ exact に戻すための橋。
-/
theorem dvd_mul_right_iff_dvd_of_coprime
    {p q n : ℕ}
    (hCoprime : Nat.Coprime p q) :
    q ∣ n * p ↔ q ∣ n := by
  constructor
  · intro h
    apply hCoprime.symm.dvd_of_dvd_mul_left
    simpa [Nat.mul_comm] using h
  · rintro ⟨k, hk⟩
    refine ⟨k * p, ?_⟩
    calc
      n * p = (q * k) * p := by rw [hk]
      _ = q * (k * p) := by simp [Nat.mul_assoc]

namespace HasUnitCarry

/--
canonical residual slope が rational 側なら、
既約な自然数 `p/q` と scaled rational certificate を同時に得られる。

`p,q` も `Coprime p q` も primitive data ではない。
-/
theorem exists_reduced_scaledRationalSlope_of_not_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hNotIrr : ¬ Irrational (residualSlope β)) :
    ∃ p q : ℕ,
      0 < q ∧
        p ≤ q ∧
          Nat.Coprime p q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) ∧
              IsScaledRationalSlope β p q := by
  obtain ⟨p, q, hq, hpq, hCoprime, hSlope⟩ :=
    exists_reduced_nat_ratio_of_not_irrational_unitInterval
      hNotIrr U.residualSlope_mem_unitInterval
  refine ⟨p, q, hq, hpq, hCoprime, hSlope, ?_⟩
  exact U.residualSlope_scaledRational_of_eq_div hq hSlope

/--
canonical slope の rational/irrational 分岐を、rational 側では既約分数 witness まで強めた形。
-/
theorem residualSlope_irrational_or_exists_reduced_natRatio
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    Irrational (residualSlope β) ∨
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            Nat.Coprime p q ∧
              residualSlope β =
                (p : ℝ) / (q : ℝ) := by
  classical
  by_cases hIrr : Irrational (residualSlope β)
  · exact Or.inl hIrr
  · right
    obtain ⟨p, q, hq, hpq, hCoprime, hSlope, _Sscaled⟩ :=
      U.exists_reduced_scaledRationalSlope_of_not_irrational hIrr
    exact ⟨p, q, hq, hpq, hCoprime, hSlope⟩

end HasUnitCarry
end Experimental
end Collatz3
