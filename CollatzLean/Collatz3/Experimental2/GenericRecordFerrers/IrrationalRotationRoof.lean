import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.FractionalGauge
import CollatzLean.Collatz3.Experimental2.MechanicalRoofDerived
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Experimental2: 任意無理回転から作る canonical lifted roof

第11段階までで、一般 RecordFerrers の本質的 phase は整数 linear gauge を除いた
fractional slope だけで決まることを示した。

このファイルでは任意の無理数 `α ∈ (0,1)` から

* residual roof: `ρ_α(n) = floor(n α)`,
* lifted roof:   `β_α(n) = n + floor(n α)`

を構成する。

`β_α` は標準 RecordFerrers gauge `β_α(1)=1` を満たし、
`1+α` の lower mechanical roof である。また

`normalizeRoof β_α = ρ_α`

であり、その direct phase / normalized fractional phase はともに
`fract(n α)` と exact に一致する。

従って任意の irrational rotation `α ∈ (0,1)` は、
一般 RecordFerrers 理論を置く canonical ambient roof を持つ。

注意：ここでは任意の admissible path が RecordFerrers であるとは主張しない。
RecordFerrers になるためには、第10段階の canonical phase threshold compatibility が
依然として必要である。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
RecordFerrers の fractional parameter として使う無理回転条件。
primitive data を増やさず、無理性と open unit interval 条件だけを束ねる。
-/
def IsIrrationalUnitRotation (α : ℝ) : Prop :=
  Irrational α ∧ 0 < α ∧ α < 1

namespace IsIrrationalUnitRotation

/-- 無理回転パラメータは非負。 -/
theorem nonneg
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    0 ≤ α :=
  le_of_lt A.2.1

/-- 無理回転パラメータの無理性。 -/
theorem irrational
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    Irrational α :=
  A.1

/-- 無理回転パラメータは正。 -/
theorem pos
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    0 < α :=
  A.2.1

/-- 無理回転パラメータは `1` 未満。 -/
theorem lt_one
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    α < 1 :=
  A.2.2

end IsIrrationalUnitRotation

/--
回転 `α` の residual mechanical roof。

`ρ_α(n) = floor(n α)`。
-/
noncomputable def rotationResidualRoof
    (α : ℝ)
    (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * α⌋₊

/-- residual roof の原点は `0`。 -/
@[simp] theorem rotationResidualRoof_zero
    (α : ℝ) :
    rotationResidualRoof α 0 = 0 := by
  simp [rotationResidualRoof]

/-- `α < 1` なら residual roof の `1` での値は `0`。 -/
@[simp] theorem rotationResidualRoof_one_eq_zero
    {α : ℝ}
    (hα : α < 1) :
    rotationResidualRoof α 1 = 0 := by
  unfold rotationResidualRoof
  norm_num
  exact hα

/--
`α ≥ 0` なら residual roof は slope `α` の lower mechanical roof。
これは `Nat.floor` の defining cell そのもの。
-/
theorem rotationResidualRoof_isLowerMechanical
    {α : ℝ}
    (hα : 0 ≤ α) :
    IsLowerMechanicalRoof (rotationResidualRoof α) α := by
  intro n
  have hx : 0 ≤ (n : ℝ) * α :=
    mul_nonneg (Nat.cast_nonneg n) hα
  unfold rotationResidualRoof
  exact (Nat.floor_eq_iff hx).1 rfl

/-- residual roof は `α ≥ 0` で unit-carry。 -/
theorem rotationResidualRoof_hasUnitCarry
    {α : ℝ}
    (hα : 0 ≤ α) :
    HasUnitCarry (rotationResidualRoof α) :=
  (rotationResidualRoof_isLowerMechanical hα).hasUnitCarry

/--
標準 gauge に持ち上げた rotation roof。

`β_α = 1*n + ρ_α` と定義することで、第8・11段階の linear gauge theorem を
そのまま再利用する。
-/
noncomputable def irrationalRotationRoof
    (α : ℝ) : ℕ → ℕ :=
  linearLiftRoof 1 (rotationResidualRoof α)

/-- lifted roof の concrete formula `n + floor(n α)`。 -/
theorem irrationalRotationRoof_eq
    (α : ℝ)
    (n : ℕ) :
    irrationalRotationRoof α n =
      n + ⌊(n : ℝ) * α⌋₊ := by
  simp [irrationalRotationRoof, linearLiftRoof, rotationResidualRoof]

/-- `α < 1` なら lifted roof は標準 gauge `β(1)=1` を満たす。 -/
@[simp] theorem irrationalRotationRoof_one
    {α : ℝ}
    (hα : α < 1) :
    irrationalRotationRoof α 1 = 1 := by
  unfold irrationalRotationRoof linearLiftRoof
  rw [rotationResidualRoof_one_eq_zero hα]

/--
`α ≥ 0` なら lifted roof は direct slope `1+α` の lower mechanical roof。
無理性はこの mechanical fact 自体には不要。
-/
theorem irrationalRotationRoof_isLowerMechanical
    {α : ℝ}
    (hα : 0 ≤ α) :
    IsLowerMechanicalRoof (irrationalRotationRoof α) (1 + α) := by
  have M0 : IsLowerMechanicalRoof (rotationResidualRoof α) α :=
    rotationResidualRoof_isLowerMechanical hα
  have M1 :=
    (lowerMechanical_linearLiftRoof_iff
      1 (rotationResidualRoof α) α).2 M0
  simpa [irrationalRotationRoof, add_comm] using M1

/-- lifted roof は `α ≥ 0` で unit-carry。 -/
theorem irrationalRotationRoof_hasUnitCarry
    {α : ℝ}
    (hα : 0 ≤ α) :
    HasUnitCarry (irrationalRotationRoof α) :=
  (irrationalRotationRoof_isLowerMechanical hα).hasUnitCarry

/-- lifted roof の direct slope `1+α` は roof slope window を満たす。 -/
theorem irrationalRotationRoof_isRoofSlope
    {α : ℝ}
    (hα : 0 ≤ α) :
    IsRoofSlope (irrationalRotationRoof α) (1 + α) :=
  (irrationalRotationRoof_isLowerMechanical hα).isRoofSlope

/--
`α < 1` なら lifted roof を正規化すると residual roof へ exact に戻る。
-/
theorem normalizeRoof_irrationalRotationRoof_eq
    {α : ℝ}
    (hα0 : 0 ≤ α)
    (hα1 : α < 1)
    (n : ℕ) :
    normalizeRoof (irrationalRotationRoof α) n =
      rotationResidualRoof α n := by
  have U0 : HasUnitCarry (rotationResidualRoof α) :=
    rotationResidualRoof_hasUnitCarry hα0
  calc
    normalizeRoof (irrationalRotationRoof α) n =
        normalizeRoof (rotationResidualRoof α) n := by
      simpa [irrationalRotationRoof] using
        (normalizeRoof_linearLiftRoof_eq 1 U0 n)
    _ = rotationResidualRoof α n := by
      unfold normalizeRoof
      rw [rotationResidualRoof_one_eq_zero hα1]
      simp

/--
標準 lifted roof `β_α` の direct slope `1+α` の fractional slope は exact に `α`。
-/
theorem irrationalRotationRoof_fractionalRoofSlope
    {α : ℝ}
    (hα : α < 1) :
    fractionalRoofSlope (irrationalRotationRoof α) (1 + α) = α := by
  unfold fractionalRoofSlope
  rw [irrationalRotationRoof_one hα]
  norm_num

/--
linear gauge 不変性により、lifted roof の direct phase は residual roof の phase と同じ。
-/
@[simp] theorem irrationalRotationRoof_phase_eq_residualPhase
    (α : ℝ)
    (n : ℕ) :
    roofPhase (irrationalRotationRoof α) (1 + α) n =
      roofPhase (rotationResidualRoof α) α n := by
  have h :=
    roofPhase_linearLiftRoof_eq 1 (rotationResidualRoof α) α n
  simpa [irrationalRotationRoof, add_comm] using h

/--
非負入力では `Nat.floor` と `Int.floor` は同じ整数を表す。
`phase = fract` の橋にだけ使う局所補題。
-/
private theorem intFloor_eq_natFloor_of_nonneg
    {x : ℝ}
    (hx : 0 ≤ x) :
    ⌊x⌋ = (⌊x⌋₊ : ℤ) := by
  have hCell :
      ((⌊x⌋₊ : ℕ) : ℝ) ≤ x ∧
        x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 :=
    (Nat.floor_eq_iff hx).1 rfl
  apply (Int.floor_eq_iff).2
  simpa using hCell

/--
residual mechanical phase は回転 `n α` の fractional part そのもの。
-/
theorem rotationResidualRoof_phase_eq_fract
    {α : ℝ}
    (hα : 0 ≤ α)
    (n : ℕ) :
    roofPhase (rotationResidualRoof α) α n =
      Int.fract ((n : ℝ) * α) := by
  let x : ℝ := (n : ℝ) * α
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (Nat.cast_nonneg n) hα
  have hFloor : ⌊x⌋ = (⌊x⌋₊ : ℤ) :=
    intFloor_eq_natFloor_of_nonneg hx
  unfold roofPhase rotationResidualRoof
  change x - ((⌊x⌋₊ : ℕ) : ℝ) = Int.fract x
  calc
    x - ((⌊x⌋₊ : ℕ) : ℝ) =
        x - ((⌊x⌋ : ℤ) : ℝ) := by
      rw [hFloor]
      norm_num
    _ = Int.fract x := Int.self_sub_floor x

/--
lifted roof の direct phase も exact に `fract(n α)`。
-/
theorem irrationalRotationRoof_phase_eq_fract
    {α : ℝ}
    (hα : 0 ≤ α)
    (n : ℕ) :
    roofPhase (irrationalRotationRoof α) (1 + α) n =
      Int.fract ((n : ℝ) * α) := by
  rw [irrationalRotationRoof_phase_eq_residualPhase]
  exact rotationResidualRoof_phase_eq_fract hα n

/--
正規化後の fractional phase も同じ `fract(n α)`。
-/
theorem irrationalRotationRoof_fractionalPhase_eq_fract
    {α : ℝ}
    (hα0 : 0 ≤ α)
    (n : ℕ) :
    fractionalRoofPhase (irrationalRotationRoof α) (1 + α) n =
      Int.fract ((n : ℝ) * α) := by
  have U : HasUnitCarry (irrationalRotationRoof α) :=
    irrationalRotationRoof_hasUnitCarry hα0
  rw [fractionalRoofPhase_eq_roofPhase U]
  exact irrationalRotationRoof_phase_eq_fract hα0 n

/--
`α` が irrational なら direct slope `1+α` も irrational。
-/
theorem irrationalRotationRoof_directSlope_irrational
    {α : ℝ}
    (hIrr : Irrational α) :
    Irrational (1 + α) := by
  simpa using hIrr.natCast_add 1

/--
任意の無理回転 `α∈(0,1)` は、標準 gauge の lower mechanical unit-carry roof を与える。
必要な ambient data を一つの conjunction として公開する。
-/
theorem irrationalUnitRotation_ambient
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    irrationalRotationRoof α 1 = 1 ∧
      HasUnitCarry (irrationalRotationRoof α) ∧
      IsLowerMechanicalRoof (irrationalRotationRoof α) (1 + α) ∧
      IsRoofSlope (irrationalRotationRoof α) (1 + α) ∧
      Irrational (1 + α) := by
  have M := irrationalRotationRoof_isLowerMechanical A.nonneg
  exact
    ⟨irrationalRotationRoof_one A.lt_one,
      M.hasUnitCarry,
      M,
      M.isRoofSlope,
      irrationalRotationRoof_directSlope_irrational A.irrational⟩

/--
任意無理回転 roof 上の RecordFerrers path 条件を、phase threshold だけで書いた exact 形。

ambient roof の `β(1)=1` と lower mechanical 性は `α∈(0,1)` から自動で供給される。
残る本質条件は

* admissible path,
* `1 < m`,
* canonical phase threshold compatibility

である。
-/
theorem isRecordFerrersPath_irrationalRotationRoof_iff
    {α : ℝ}
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    IsRecordFerrersPath (irrationalRotationRoof α) m height ↔
      IsAdmissibleRoofPath (irrationalRotationRoof α) m height ∧
        1 < m ∧
          CanonicalPhaseThresholdCompatible
            (irrationalRotationRoof α) (1 + α) m height := by
  have M :
      IsLowerMechanicalRoof (irrationalRotationRoof α) (1 + α) :=
    irrationalRotationRoof_isLowerMechanical Arot.nonneg
  have hOne : irrationalRotationRoof α 1 = 1 :=
    irrationalRotationRoof_one Arot.lt_one
  have h :=
    isRecordFerrersPath_iff_phaseThresholdCompatible
      (β := irrationalRotationRoof α) (σ := 1 + α) M
      (m := m) (height := height)
  simpa [hOne] using h

/--
任意無理回転 roof 上で、admissibility と canonical phase threshold law から
直接 RecordFerrers を構成する。

これは「任意の無理回転が RecordFerrers になる」という主張ではない。
phase threshold law を満たす path だけを構成する。
-/
noncomputable def recordFerrersOfIrrationalRotation
    {α : ℝ}
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath (irrationalRotationRoof α) m height)
    (hm : 1 < m)
    (P : CanonicalPhaseThresholdCompatible
      (irrationalRotationRoof α) (1 + α) m height) :
    RecordFerrers (irrationalRotationRoof α) m :=
  RecordFerrers.ofCanonicalPhase
    (irrationalRotationRoof_isLowerMechanical Arot.nonneg)
    A
    (irrationalRotationRoof_one Arot.lt_one)
    hm
    P

end GenericRecordFerrers
end Experimental2
end Collatz3
