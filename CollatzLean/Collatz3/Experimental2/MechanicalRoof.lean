import CollatzLean.Collatz3.Experimental2.SlopeWindow
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Collatz3 Experimental2: mechanical roof の薄い定義

linear part と residual を定義に保存せず、
屋根 `β` 自身が slope `σ` の lower / upper cell を選ぶことだけを表す。
-/

namespace Collatz3
namespace Experimental2

def IsLowerMechanicalRoof
    (β : ℕ → ℕ)
    (σ : ℝ) : Prop :=
  ∀ n : ℕ, IsNatFloor (β n) ((n : ℝ) * σ)

def IsUpperMechanicalRoof
    (β : ℕ → ℕ)
    (σ : ℝ) : Prop :=
  β 0 = 0 ∧
    ∀ n : ℕ, 0 < n →
      IsNatUpperCell (β n) ((n : ℝ) * σ)

namespace IsLowerMechanicalRoof

/-- lower mechanical roof は concrete な Nat.floor 公式。 -/
theorem eq_natFloor
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : 0 ≤ σ)
    (n : ℕ) :
    β n = ⌊(n : ℝ) * σ⌋₊ := by
  have hNonneg : 0 ≤ (n : ℝ) * σ := by positivity
  symm
  exact (Nat.floor_eq_iff hNonneg).2 (by
    simpa [IsNatFloor] using M n)

end IsLowerMechanicalRoof
end Experimental2
end Collatz3
