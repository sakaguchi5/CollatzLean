import CollatzLean.Collatz3.Experimental.UnitCarryClassification

/-!
# Collatz3 experimental: mechanical roof の rotation phase

homogenized slope の floor 型が得られた場合、residual を取り除いた実数 phase

`phase(n) = nρ - γ(n)`

を導入する。

`IsMechanicalSlope` の下では `0 ≤ phase(n) < 1` であり、
carry cocycle は

`phase(a+b) = phase(a) + phase(b) - c(a,b)`

という circle rotation の wrap equation になる。

したがって carry `1` は phase 和が 1 を跨いだことと exact に同値。
一歩 carry word は rotation by `ρ` の mechanical coding になる。
-/

namespace Collatz3
namespace Experimental

/-- residual が各 `nρ` の lower floor cell を選んでいること。 -/
def IsMechanicalSlope
    (β : ℕ → ℕ)
    (ρ : ℝ) : Prop :=
  ∀ n : ℕ,
    IsNatFloor (roofResidual β n) ((n : ℝ) * ρ)

/-- circle 上の phase。floor API の fractional-part に相当する。 -/
def roofPhase
    (β : ℕ → ℕ)
    (ρ : ℝ)
    (n : ℕ) : ℝ :=
  (n : ℝ) * ρ - (roofResidual β n : ℝ)

namespace HasUnitCarry

/--
no-integral-multiple な homogenized slope は自動的に mechanical slope になる。
`n=0` だけは `β(0)=0` から処理する。
-/
theorem isMechanicalSlope_of_homogenized_noIntegralMultiple
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (S : IsHomogenizedSlope β ρ)
    (H : HasNoIntegralMultiple ρ) :
    IsMechanicalSlope β ρ := by
  intro n
  cases n with
  | zero =>
      have hZero := U.roofResidual_zero
      simp [IsNatFloor, hZero]
  | succ n =>
      exact residual_isNatFloor_of_noIntegralMultiple
        S H (by omega)

/-- mechanical phase は 0 以上。 -/
theorem roofPhase_nonneg
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (n : ℕ) :
    0 ≤ roofPhase β ρ n := by
  have hFloor := (M n).1
  unfold roofPhase
  linarith

/-- mechanical phase は 1 未満。 -/
theorem roofPhase_lt_one
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (n : ℕ) :
    roofPhase β ρ n < 1 := by
  have hFloor := (M n).2
  unfold roofPhase
  linarith

/-- phase at 1 は slope `ρ` そのもの。 -/
@[simp] theorem roofPhase_one
    (β : ℕ → ℕ)
    (ρ : ℝ) :
    roofPhase β ρ 1 = ρ := by
  simp [roofPhase, roofResidual]

/--
carry cocycle の circle phase 版。

`phase(a+b) = phase(a) + phase(b) - c(a,b)`。
-/
theorem roofPhase_add
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (ρ : ℝ)
    (a b : ℕ) :
    roofPhase β ρ (a + b) =
      roofPhase β ρ a + roofPhase β ρ b -
        (roofCarry β a b : ℝ) := by
  have hResidual := U.residual_add_eq a b
  have hResidualR :
      (roofResidual β (a + b) : ℝ) =
        (roofResidual β a : ℝ) +
          (roofResidual β b : ℝ) +
            (roofCarry β a b : ℝ) := by
    exact_mod_cast hResidual
  unfold roofPhase
  push_cast
  rw [hResidualR]
  ring

/--
mechanical phase では carry `1` と circle wrap が exact に同値。

`c(a,b)=1 <-> 1 ≤ phase(a)+phase(b)`。
-/
theorem carry_eq_one_iff_phase_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (a b : ℕ) :
    roofCarry β a b = 1 ↔
      1 ≤ roofPhase β ρ a + roofPhase β ρ b := by
  have hPhase := U.roofPhase_add ρ a b
  have hNonneg := roofPhase_nonneg M (a + b)
  have hLtOne := roofPhase_lt_one M (a + b)
  constructor
  · intro hOne
    rw [hOne] at hPhase
    norm_num at hPhase
    linarith
  · intro hWrap
    rcases U.carry_eq_zero_or_one a b with hZero | hOne
    · rw [hZero] at hPhase
      norm_num at hPhase
      linarith
    · exact hOne

/-- carry `0` は phase 和が 1 未満であることと同値。 -/
theorem carry_eq_zero_iff_phase_noWrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (a b : ℕ) :
    roofCarry β a b = 0 ↔
      roofPhase β ρ a + roofPhase β ρ b < 1 := by
  constructor
  · intro hZero
    have hPhase := U.roofPhase_add ρ a b
    have hLtOne := roofPhase_lt_one M (a + b)
    rw [hZero] at hPhase
    norm_num at hPhase
    linarith
  · intro hNoWrap
    rcases U.carry_eq_zero_or_one a b with hZero | hOne
    · exact hZero
    · have hWrap := (U.carry_eq_one_iff_phase_wrap M a b).1 hOne
      linarith

/--
一歩 carry word は rotation by `ρ` の threshold coding。

`w(a)=1 <-> 1 ≤ phase(a)+ρ`。
-/
theorem carryWord_eq_one_iff_rotation_wrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (a : ℕ) :
    carryWord β a = 1 ↔
      1 ≤ roofPhase β ρ a + ρ := by
  simpa [carryWord] using
    (U.carry_eq_one_iff_phase_wrap M a 1)

/--
phase の一歩更新式。

`phase(a+1) = phase(a) + ρ - w(a)`。
-/
theorem roofPhase_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (ρ : ℝ)
    (a : ℕ) :
    roofPhase β ρ (a + 1) =
      roofPhase β ρ a + ρ - (carryWord β a : ℝ) := by
  simpa [carryWord] using U.roofPhase_add ρ a 1

/--
integer boundary が無い場合、rotation wrap の `≤` は strict `>` に強化できる。
これは irrational mechanical word の通常の threshold 形。
-/
theorem carryWord_eq_one_iff_rotation_strictWrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (M : IsMechanicalSlope β ρ)
    (H : HasNoIntegralMultiple ρ)
    (a : ℕ) :
    carryWord β a = 1 ↔
      1 < roofPhase β ρ a + ρ := by
  have hWeak := U.carryWord_eq_one_iff_rotation_wrap M a
  have hBoundaryNe : roofPhase β ρ a + ρ ≠ 1 := by
    intro hEq
    apply H (a + 1) (roofResidual β a + 1) (by omega)
    have hCast :
        (((a + 1 : ℕ) : ℝ) * ρ) =
          ((roofResidual β a + 1 : ℕ) : ℝ) := by
      unfold roofPhase at hEq
      push_cast at hEq ⊢
      nlinarith
    exact hCast
  constructor
  · intro hOne
    have hLe := hWeak.1 hOne
    rcases lt_or_eq_of_le hLe with hLt | hEq
    · exact hLt
    · exact False.elim (hBoundaryNe hEq.symm)
  · intro hStrict
    exact hWeak.2 (le_of_lt hStrict)

end HasUnitCarry
end Experimental
end Collatz3
