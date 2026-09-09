import CollatzLean.Collatz3.Experimental2.MechanicalRoof

/-!
# Collatz3 Experimental2: mechanical roof の concrete formula と slope wrapper

薄い cell 定義から、`IsRoofSlope` および concrete floor / ceil 公式を derived theorem として戻す。
-/

namespace Collatz3
namespace Experimental2

namespace IsLowerMechanicalRoof

/-- lower mechanical roof は自動的に roof slope window を満たす。 -/
theorem isRoofSlope
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ) :
    IsRoofSlope β σ := by
  intro n hn
  have h := M n
  exact ⟨h.1, le_of_lt h.2⟩

/-- lower mechanical slope は非負。 -/
theorem slope_nonneg
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ) :
    0 ≤ σ := by
  have h := (M 1).1
  norm_num at h
  exact le_trans (Nat.cast_nonneg (β 1)) h

/-- lower mechanical roof の floor 公式。外部から `σ≥0` を渡す必要はない。 -/
theorem eq_natFloor'
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (n : ℕ) :
    β n = ⌊(n : ℝ) * σ⌋₊ :=
  M.eq_natFloor M.slope_nonneg n

end IsLowerMechanicalRoof

namespace IsUpperMechanicalRoof

/-- upper mechanical roof も roof slope window を満たす。 -/
theorem isRoofSlope
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ) :
    IsRoofSlope β σ := by
  intro n hn
  have h := M.2 n hn
  exact ⟨le_of_lt h.1, h.2⟩

/-- upper mechanical slope は正。 -/
theorem slope_pos
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ) :
    0 < σ := by
  have h := (M.2 1 (by omega)).1
  norm_num at h
  exact lt_of_le_of_lt (Nat.cast_nonneg (β 1)) h

/--
upper mechanical roof の concrete ceil 公式。

`β(n) = ceil(nσ) - 1`。
-/
theorem eq_natCeil_sub_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ)
    (n : ℕ) :
    β n = ⌈(n : ℝ) * σ⌉₊ - 1 := by
  by_cases hn : n = 0
  · subst n
    simp [M.1]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have h := M.2 n hnPos
    have hCeil :
        ⌈(n : ℝ) * σ⌉₊ = β n + 1 := by
      apply (Nat.ceil_eq_iff (by omega)).2
      constructor
      · simpa using h.1
      · simpa using h.2
    omega

end IsUpperMechanicalRoof
end Experimental2
end Collatz3
