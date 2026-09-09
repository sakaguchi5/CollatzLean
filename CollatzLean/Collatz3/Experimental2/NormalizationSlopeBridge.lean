import CollatzLean.Collatz3.Experimental2.Normalization
import CollatzLean.Collatz3.Experimental2.SlopeWindow
import CollatzLean.Collatz3.Experimental2.SlopeExistence
import CollatzLean.Collatz3.Experimental2.MechanicalRoof
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: 正規化と slope の移送

正規化 `normalizeRoof β` は carry だけでなく slope window / mechanical cell も
整数 anchor `β(1)` だけ平行移動して保存する。

このファイルは旧 Experimental の residual slope 理論と、Experimental2 の direct roof slope 理論を
接続する derived bridge であり、新しい primitive data は追加しない。
-/

namespace Collatz3
namespace Experimental2


/-- direct slope から整数 anchor を除いた normalized slope は `[0,1]` に入る。 -/
theorem normalizedSlope_mem_unitInterval
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ) :
    0 ≤ σ - (β 1 : ℝ) ∧ σ - (β 1 : ℝ) ≤ 1 := by
  have h := roofSlope_mem_anchorInterval S
  constructor <;> linarith
namespace HasUnitCarry

/--
direct roof slope `σ` と normalized roof slope `σ - β(1)` は exact に同値。
-/
theorem roofSlope_normalizeRoof_iff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ} :
    IsRoofSlope β σ ↔
      IsRoofSlope (normalizeRoof β) (σ - (β 1 : ℝ)) := by
  constructor
  · intro S n hn
    have hS := S n hn
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) + (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    constructor <;> nlinarith
  · intro S n hn
    have hS := S n hn
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) + (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    constructor <;> nlinarith

/-- lower mechanical 性も正規化で slope を `β(1)` だけ平行移動して保存される。 -/
theorem lowerMechanical_normalizeRoof_iff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ} :
    IsLowerMechanicalRoof β σ ↔
      IsLowerMechanicalRoof (normalizeRoof β) (σ - (β 1 : ℝ)) := by
  constructor
  · intro M n
    have h := M n
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) +
            (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    have hShift :
        (n : ℝ) * (σ - (β 1 : ℝ)) =
          (n : ℝ) * σ - (n : ℝ) * (β 1 : ℝ) := by
      ring
    have hNorm :
        (normalizeRoof β n : ℝ) =
          (β n : ℝ) - (n : ℝ) * (β 1 : ℝ) := by
      linarith [hEqR]
    constructor
    · rw [hShift, hNorm]
      linarith [h.1]
    · rw [hShift, hNorm]
      linarith [h.2]
  · intro M n
    have h := M n
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) +
            (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    have hShift :
        (n : ℝ) * (σ - (β 1 : ℝ)) =
          (n : ℝ) * σ - (n : ℝ) * (β 1 : ℝ) := by
      ring
    constructor
    · linarith [h.1, hEqR, hShift]
    · linarith [h.2, hEqR, hShift]

/-- upper mechanical 性も同様に正規化で保存される。 -/
theorem upperMechanical_normalizeRoof_iff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ} :
    IsUpperMechanicalRoof β σ ↔
      IsUpperMechanicalRoof (normalizeRoof β) (σ - (β 1 : ℝ)) := by
  constructor
  · intro M
    refine ⟨U.normalizeRoof_zero, ?_⟩
    intro n hn
    have h := M.2 n hn
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) +
            (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    have hShift :
        (n : ℝ) * (σ - (β 1 : ℝ)) =
          (n : ℝ) * σ - (n : ℝ) * (β 1 : ℝ) := by
      ring
    constructor
    · linarith [h.1, hEqR, hShift]
    · linarith [h.2, hEqR, hShift]
  · intro M
    refine ⟨U.zero_eq, ?_⟩
    intro n hn
    have h := M.2 n hn
    have hEqNat := U.eq_linear_add_normalizeRoof n
    have hEqR :
        (β n : ℝ) =
          (n : ℝ) * (β 1 : ℝ) +
            (normalizeRoof β n : ℝ) := by
      exact_mod_cast hEqNat
    have hShift :
        (n : ℝ) * (σ - (β 1 : ℝ)) =
          (n : ℝ) * σ - (n : ℝ) * (β 1 : ℝ) := by
      ring
    constructor
    · linarith [h.1, hEqR, hShift]
    · linarith [h.2, hEqR, hShift]

end HasUnitCarry
end Experimental2
end Collatz3
