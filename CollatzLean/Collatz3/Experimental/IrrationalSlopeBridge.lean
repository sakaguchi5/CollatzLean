import CollatzLean.Collatz3.Experimental.HomogenizedSlopeUniqueness
import Mathlib.NumberTheory.Real.Irrational

/-!
# Collatz3 experimental: irrational slope から integer-boundary-free への bridge

分類層で使っている最小条件 `HasNoIntegralMultiple ρ` を、
標準的な `Irrational ρ` から導く。

この中心 bridge 自体には `HasUnitCarry` も roof も不要。
-/

namespace Collatz3
namespace Experimental

/--
無理数 `ρ` の正整数倍は自然数の整数境界に乗らない。

`nρ = k` なら `ρ = k/n` となって有理数になるため矛盾する。
-/
theorem irrational_hasNoIntegralMultiple
    {ρ : ℝ}
    (hIrr : Irrational ρ) :
    HasNoIntegralMultiple ρ := by
  intro n k hn hEq
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hρ :
      ρ = (k : ℝ) / (n : ℝ) := by
    apply (eq_div_iff hnR).2
    nlinarith [hEq]
  apply hIrr.ne_rational (k : ℤ) (n : ℤ)
  simpa only [Int.cast_natCast] using hρ

/-- canonical residual slope が無理数なら、分類層の非整数境界条件が自動的に得られる。 -/
theorem residualSlope_hasNoIntegralMultiple_of_irrational
    {β : ℕ → ℕ}
    (hIrr : Irrational (residualSlope β)) :
    HasNoIntegralMultiple (residualSlope β) := by
  exact irrational_hasNoIntegralMultiple hIrr

namespace HasUnitCarry

/--
canonical residual slope が無理数なら、全正整数 `n` で residual は exact floor cell に入る。

これは
`HasUnitCarry -> canonical slope existence -> irrational bridge -> floor classification`
を一本にした corollary。
-/
theorem residual_isNatFloor_of_residualSlope_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hIrr : Irrational (residualSlope β))
    {n : ℕ}
    (hn : 0 < n) :
    IsNatFloor
      (roofResidual β n)
      ((n : ℝ) * residualSlope β) := by
  exact residual_isNatFloor_of_noIntegralMultiple
    U.residualSlope_isHomogenizedSlope
    (irrational_hasNoIntegralMultiple hIrr)
    hn

/-- 無理 canonical slope では slope window の両端が strict。 -/
theorem residual_strict_window_of_residualSlope_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hIrr : Irrational (residualSlope β))
    {n : ℕ}
    (hn : 0 < n) :
    (roofResidual β n : ℝ) <
        (n : ℝ) * residualSlope β ∧
      (n : ℝ) * residualSlope β <
        (roofResidual β n : ℝ) + 1 := by
  exact residual_strict_window_of_noIntegralMultiple
    U.residualSlope_isHomogenizedSlope
    (irrational_hasNoIntegralMultiple hIrr)
    hn

end HasUnitCarry
end Experimental
end Collatz3
