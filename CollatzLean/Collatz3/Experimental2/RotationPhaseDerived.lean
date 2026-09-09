import CollatzLean.Collatz3.Experimental2.RotationPhase
import CollatzLean.Collatz3.Experimental2.CarryWord

/-!
# Collatz3 Experimental2: rotation phase の一歩 API

二項 phase law から一歩更新式と carry-word threshold coding を derived theorem として戻す。
-/

namespace Collatz3
namespace Experimental2

/-- phase at `1` は direct slope から integer anchor を引いた量。 -/
@[simp] theorem roofPhase_one
    (β : ℕ → ℕ)
    (σ : ℝ) :
    roofPhase β σ 1 = σ - (β 1 : ℝ) := by
  simp [roofPhase]

/-- phase の一歩更新式。 -/
theorem roofPhase_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (σ : ℝ)
    (a : ℕ) :
    roofPhase β σ (a + 1) =
      roofPhase β σ a + (σ - (β 1 : ℝ)) -
        (carryWord β a : ℝ) := by
  simpa [carryWord] using roofPhase_add U σ a 1

/-- lower convention の一歩 carry は rotation wrap の threshold coding。 -/
theorem carryWord_eq_one_iff_lowerRotation_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (a : ℕ) :
    carryWord β a = 1 ↔
      1 ≤ roofPhase β σ a + (σ - (β 1 : ℝ)) := by
  simpa [carryWord] using
    (carry_eq_one_iff_lowerPhase_wrap U M a 1)

/-- upper convention では equality boundary を除き strict threshold になる。 -/
theorem carryWord_eq_one_iff_upperRotation_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ)
    (a : ℕ) :
    carryWord β a = 1 ↔
      1 < roofPhase β σ a + (σ - (β 1 : ℝ)) := by
  simpa [carryWord] using
    (carry_eq_one_iff_upperPhase_wrap U M a 1)

/-- normalized roof では phase at `1` が slope 自身になる。 -/
@[simp] theorem roofPhase_normalizeRoof_one
    (β : ℕ → ℕ)
    (ρ : ℝ) :
    roofPhase (normalizeRoof β) ρ 1 = ρ := by
  simp [roofPhase, normalizeRoof]

end Experimental2
end Collatz3
