import CollatzLean.Collatz3.Experimental
import CollatzLean.Collatz3.Experimental2

set_option linter.style.header false

/-!
# Collatz3 Experimental / Experimental2 compatibility regression

このファイルは stable `Experimental2.lean` からは import しない。
旧 Experimental を regression oracle として読み、新設計の基礎定義・正規化・slope window が
旧概念と lossless に対応することを theorem で確認するための専用入口。
-/

namespace Collatz3
namespace Experimental2Compatibility

/-- 旧 `HasUnitCarry` と新しい二公理分解版は同値。 -/
theorem hasUnitCarry_iff
    {β : ℕ → ℕ} :
    Experimental.HasUnitCarry β ↔ Experimental2.HasUnitCarry β := by
  constructor
  · intro U
    exact ⟨
      (fun a b => (U a b).1),
      (fun a b => (U a b).2)⟩
  · rintro ⟨L, H⟩
    intro a b
    exact ⟨L a b, H a b⟩

/-- critical depth は definitionally 同一。 -/
theorem criticalDepth_eq
    (β : ℕ → ℕ)
    (m : ℕ) :
    Experimental.criticalDepth β m = Experimental2.criticalDepth β m := by
  rfl

/-- 二項 carry も definitionally 同一。 -/
theorem roofCarry_eq
    (β : ℕ → ℕ)
    (a b : ℕ) :
    Experimental.roofCarry β a b = Experimental2.roofCarry β a b := by
  rfl

/-- 旧 `roofResidual` は新 `normalizeRoof` と definitionally 同一。 -/
theorem roofResidual_eq_normalizeRoof
    (β : ℕ → ℕ)
    (n : ℕ) :
    Experimental.roofResidual β n = Experimental2.normalizeRoof β n := by
  rfl

/-- 一歩 carry word の定義も一致する。 -/
theorem carryWord_eq
    (β : ℕ → ℕ)
    (n : ℕ) :
    Experimental.carryWord β n = Experimental2.carryWord β n := by
  rfl

/-- carry-word weight も全長で一致する。 -/
theorem carryWordWeight_eq
    (β : ℕ → ℕ)
    (a r : ℕ) :
    Experimental.carryWordWeight β a r =
      Experimental2.carryWordWeight β a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [Experimental.carryWordWeight,
        Experimental2.carryWordWeight, ih, carryWord_eq]

/-- 旧 admissible roof path と新しい3 predicate 分解版は同値。 -/
theorem admissibleRoofPath_iff
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) :
    Experimental.IsAdmissibleRoofPath β m height ↔
      Experimental2.IsAdmissibleRoofPath β m height := by
  rfl

/-- 旧 roof cut と新 `IsProperRoofCut` は同値。 -/
theorem roofCut_iff_properRoofCut
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a : ℕ) :
    Experimental.IsRoofCut β m height a ↔
      Experimental2.IsProperRoofCut β m height a := by
  rfl

/-- local depth は definitionally 同一。 -/
theorem localDepth_eq
    (height : ℕ → ℕ)
    (a j : ℕ) :
    Experimental.localDepth height a j = Experimental2.localDepth height a j := by
  rfl

/-- 旧 global defect と新 derived defect は同一。 -/
theorem roofDefect_eq
    (β : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) :
    Experimental.roofDefect β a rs = Experimental2.roofDefect β a rs := by
  rfl

/-- 旧 floor-cell predicate と新 predicate は同一。 -/
theorem isNatFloor_iff
    (k : ℕ)
    (x : ℝ) :
    Experimental.IsNatFloor k x ↔ Experimental2.IsNatFloor k x := by
  rfl

/--
旧 homogenized residual slope certificate は、新 normalized roof の direct `IsRoofSlope` と同一。
-/
theorem homogenizedSlope_iff_normalizedRoofSlope
    (β : ℕ → ℕ)
    (ρ : ℝ) :
    Experimental.IsHomogenizedSlope β ρ ↔
      Experimental2.IsRoofSlope (Experimental2.normalizeRoof β) ρ := by
  rfl

/-- 旧 rational scaled residual certificate も normalized roof 上の新 certificate と同一。 -/
theorem scaledRationalSlope_iff_normalized
    (β : ℕ → ℕ)
    (p q : ℕ) :
    Experimental.IsScaledRationalSlope β p q ↔
      Experimental2.IsScaledRationalSlope
        (Experimental2.normalizeRoof β) p q := by
  rfl

/--
旧 canonical `residualSlope` は、新理論では normalized roof の exact slope witness になる。
-/
theorem old_residualSlope_is_new_normalizedRoofSlope
    {β : ℕ → ℕ}
    (U : Experimental.HasUnitCarry β) :
    Experimental2.IsRoofSlope
      (Experimental2.normalizeRoof β)
      (Experimental.residualSlope β) := by
  exact (homogenizedSlope_iff_normalizedRoofSlope β
    (Experimental.residualSlope β)).1
      U.residualSlope_isHomogenizedSlope

/--
旧 residual slope に integer anchor `β(1)` を戻せば、新 direct roof slope witness になる。
-/
theorem old_residualSlope_add_anchor_is_new_roofSlope
    {β : ℕ → ℕ}
    (U : Experimental.HasUnitCarry β) :
    Experimental2.IsRoofSlope β
      (Experimental.residualSlope β + (β 1 : ℝ)) := by
  have U2 : Experimental2.HasUnitCarry β := hasUnitCarry_iff.mp U
  have SNorm := old_residualSlope_is_new_normalizedRoofSlope U
  apply (U2.roofSlope_normalizeRoof_iff
    (σ := Experimental.residualSlope β + (β 1 : ℝ))).2
  simpa using SNorm

end Experimental2Compatibility
end Collatz3
