import CollatzLean.Collatz3.Experimental.NonnegativeRationalSlopeExtraction

/-!
# Collatz3 experimental: unit-carry roof の slope 完全分類

ここまでの Experimental 層を一本に束ねる。

`HasUnitCarry β` だけから canonical slope `residualSlope β` が存在し、一意である。

その slope は必ず次のどちらか:

1. irrational case:
   全正整数 `n` で residual は `nρ` の exact floor cell に入る。

2. rational case:
   `ρ = p/q`, `0 < q`, `p ≤ q` が内部で自動的に得られ、
   Nat だけの scaled window へ降りる。
   分母境界ではさらに
   * lower 型 `γ(q)=p`
   * upper 型 `γ(q)+1=p`
   の二型に分かれ、その型は全正倍数へ伝播する。

したがって `p,q` も slope も primitive data として保存する必要はない。
-/

namespace Collatz3
namespace Experimental

namespace HasUnitCarry

/--
unit-carry roof の canonical slope 完全分類。

irrational 側では全 residual が exact floor cell に入り、
rational 側では自然数比 `p/q` が自動抽出され、
非境界点の strict window と分母境界の lower / upper 二型まで得られる。
-/
theorem completeSlopeClassification
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    (
      Irrational (residualSlope β) ∧
        ∀ n : ℕ, 0 < n →
          IsNatFloor
            (roofResidual β n)
            ((n : ℝ) * residualSlope β)
    ) ∨
    (
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) ∧
              IsScaledRationalSlope β p q ∧
              (∀ n : ℕ, 0 < n → ¬ q ∣ n * p →
                q * roofResidual β n < n * p ∧
                  n * p < q * (roofResidual β n + 1)) ∧
              (
                (
                  roofResidual β q = p ∧
                    ∀ k : ℕ,
                      roofResidual β (k * q) = k * p
                ) ∨
                (
                  roofResidual β q + 1 = p ∧
                    ∀ k : ℕ, 0 < k →
                      roofResidual β (k * q) + 1 = k * p
                )
              )
    ) := by
  classical
  by_cases hIrr : Irrational (residualSlope β)
  · left
    refine ⟨hIrr, ?_⟩
    intro n hn
    exact
      U.residual_isNatFloor_of_residualSlope_irrational
        hIrr hn
  · right
    obtain ⟨p, q, hq, hpq, hSlope, Sscaled⟩ :=
      U.exists_scaledRationalSlope_of_not_irrational hIrr
    refine ⟨p, q, hq, hpq, hSlope, Sscaled, ?_, ?_⟩
    · intro n hn hNotDvd
      exact
        rationalSlope_strictWindow_of_not_dvd
          Sscaled hn hNotDvd
    · rcases
        rationalSlope_denominator_two_boundary_types Sscaled
          with hLower | hUpper
      · left
        refine ⟨hLower, ?_⟩
        exact
          U.rationalSlope_lowerBoundary_propagates
            Sscaled hLower
      · right
        refine ⟨hUpper, ?_⟩
        exact
          U.rationalSlope_upperBoundary_propagates
            Sscaled hUpper

/--
完全分類の短い形。

`HasUnitCarry β` だけから、

* irrational mechanical/floor 型
* rational lower-boundary 型
* rational upper-boundary 型

の三者のどれかに必ず入る。

rational 側の `p,q` は external parameter ではない。
-/
theorem completeSlopeTrichotomy
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    (
      Irrational (residualSlope β) ∧
        ∀ n : ℕ, 0 < n →
          IsNatFloor
            (roofResidual β n)
            ((n : ℝ) * residualSlope β)
    ) ∨
    (
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) ∧
            roofResidual β q = p
    ) ∨
    (
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) ∧
            roofResidual β q + 1 = p
    ) := by
  rcases U.completeSlopeClassification with hIrr | hRat
  · exact Or.inl hIrr
  · rcases hRat with
      ⟨p, q, hq, hpq, hSlope, _Sscaled, _hStrict, hBoundary⟩
    rcases hBoundary with hLower | hUpper
    · exact Or.inr <| Or.inl
        ⟨p, q, hq, hpq, hSlope, hLower.1⟩
    · exact Or.inr <| Or.inr
        ⟨p, q, hq, hpq, hSlope, hUpper.1⟩

end HasUnitCarry
end Experimental
end Collatz3
