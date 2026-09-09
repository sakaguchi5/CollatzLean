import CollatzLean.Collatz3.Experimental2.SlopeApproximation

/-!
# Collatz3 Experimental2: 計算可能近似の exact certificate

`lowerSlopeApprox` / `upperSlopeApprox` は実行可能な `ℚ` 値である。
ここでは exact Real slope `σ` がその間に入ることを theorem として接続する。
-/

namespace Collatz3
namespace Experimental2

/-- 有理 lower 近似を `ℝ` に cast すると通常の lower ratio になる。 -/
theorem lowerSlopeApprox_cast
    (β : ℕ → ℕ)
    (N : ℕ) :
    ((lowerSlopeApprox β N : ℚ) : ℝ) =
      (β (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  norm_num [lowerSlopeApprox]

/-- 有理 upper 近似を `ℝ` に cast すると通常の upper ratio になる。 -/
theorem upperSlopeApprox_cast
    (β : ℕ → ℕ)
    (N : ℕ) :
    ((upperSlopeApprox β N : ℚ) : ℝ) =
      ((β (N + 1) : ℝ) + 1) / ((N + 1 : ℕ) : ℝ) := by
  norm_num [upperSlopeApprox]

/--
任意の exact roof slope は、有限計算された有理 lower / upper 近似の間に入る。
-/
theorem roofSlope_between_approximations
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (N : ℕ) :
    ((lowerSlopeApprox β N : ℚ) : ℝ) ≤ σ ∧
      σ ≤ ((upperSlopeApprox β N : ℚ) : ℝ) := by
  have hn : 0 < N + 1 := by omega
  have hnR : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have h := S (N + 1) hn
  rw [lowerSlopeApprox_cast, upperSlopeApprox_cast]
  constructor
  · apply (div_le_iff₀ hnR).2
    simpa [mul_comm] using h.1
  · apply (le_div_iff₀ hnR).2
    simpa [mul_comm] using h.2

/-- lower 近似から exact slope までの誤差は高々 `1/(N+1)`。 -/
theorem roofSlope_sub_lowerApprox_le
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (N : ℕ) :
    σ - ((lowerSlopeApprox β N : ℚ) : ℝ) ≤
      1 / ((N + 1 : ℕ) : ℝ) := by
  have hBounds := roofSlope_between_approximations S N
  have hWidthR :
      ((upperSlopeApprox β N : ℚ) : ℝ) -
          ((lowerSlopeApprox β N : ℚ) : ℝ) =
        1 / ((N + 1 : ℕ) : ℝ) := by
    rw [upperSlopeApprox_cast, lowerSlopeApprox_cast]
    have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  linarith

end Experimental2
end Collatz3
