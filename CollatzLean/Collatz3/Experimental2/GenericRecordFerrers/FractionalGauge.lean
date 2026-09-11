import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.LinearGauge
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.MechanicalPhase
import CollatzLean.Collatz3.Experimental2.NormalizationSlopeBridge
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: RecordFerrers の fractional gauge

第8段階では、屋根と path に同じ整数直線 `c*n` を加えても
record/carry 幾何が exact に変わらないことを示した。
第10段階では、その carry law を lower mechanical phase threshold へ exact に移した。

このファイルでは両者を実数 slope 側で接続する。

* `βᶜ(n) = c*n + β(n)` と slope `σ+c` の phase は元の phase と同じ。
* direct slope `σ` から整数 anchor `β(1)` を除いた
  `σ - β(1)` を fractional slope とする。
* `normalizeRoof β` の fractional slope phase は direct roof の phase と exact に同じ。
* irrational slope なら fractional slope は irrational で、roof slope の場合は strict に `(0,1)` に入る。
* canonical phase threshold law も linear gauge で exact に不変。

重要なのは、`normalizeRoof β` 自体を新しい RecordFerrers path とみなさないことである。
ここで正規化するのは phase 座標であり、path の strictness を別物に置き換えない。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
direct roof slope から整数 anchor `β(1)` を除いた fractional slope。
-/
def fractionalRoofSlope
    (β : ℕ → ℕ)
    (σ : ℝ) : ℝ :=
  σ - (β 1 : ℝ)

/--
整数 linear lift と slope の同じ整数 shift は fractional slope を変えない。
-/
@[simp] theorem fractionalRoofSlope_linearLiftRoof
    (c : ℕ)
    (β : ℕ → ℕ)
    (σ : ℝ) :
    fractionalRoofSlope (linearLiftRoof c β) (σ + (c : ℝ)) =
      fractionalRoofSlope β σ := by
  unfold fractionalRoofSlope
  rw [linearLiftRoof_one]
  push_cast
  ring

/--
屋根へ `c*n` を加え、同時に slope を `σ+c` へ動かすと phase は exact に変わらない。
-/
@[simp] theorem roofPhase_linearLiftRoof_eq
    (c : ℕ)
    (β : ℕ → ℕ)
    (σ : ℝ)
    (n : ℕ) :
    roofPhase (linearLiftRoof c β) (σ + (c : ℝ)) n =
      roofPhase β σ n := by
  unfold roofPhase linearLiftRoof
  push_cast
  ring

/--
roof slope window 自体も整数 linear gauge で exact に不変。
-/
theorem roofSlope_linearLiftRoof_iff
    (c : ℕ)
    (β : ℕ → ℕ)
    (σ : ℝ) :
    IsRoofSlope (linearLiftRoof c β) (σ + (c : ℝ)) ↔
      IsRoofSlope β σ := by
  unfold IsRoofSlope
  constructor
  · intro S n hn
    have h := S n hn
    unfold linearLiftRoof at h
    push_cast at h
    constructor <;> nlinarith
  · intro S n hn
    have h := S n hn
    unfold linearLiftRoof
    push_cast
    constructor <;> nlinarith

/--
lower mechanical roof も整数 linear gauge で exact に不変。
-/
theorem lowerMechanical_linearLiftRoof_iff
    (c : ℕ)
    (β : ℕ → ℕ)
    (σ : ℝ) :
    IsLowerMechanicalRoof (linearLiftRoof c β) (σ + (c : ℝ)) ↔
      IsLowerMechanicalRoof β σ := by
  unfold IsLowerMechanicalRoof
  constructor
  · intro M n
    have h := M n
    unfold IsNatFloor at h ⊢
    unfold linearLiftRoof at h
    push_cast at h
    constructor <;> nlinarith
  · intro M n
    have h := M n
    unfold IsNatFloor at h ⊢
    unfold linearLiftRoof
    push_cast
    constructor <;> nlinarith

/--
unit-carry roof では、正規化 roof の fractional slope phase と direct roof の phase が exact に一致する。

`β(n) = n*β(1) + normalizeRoof β(n)` の整数線形成分が slope 側の同じ成分と相殺される。
-/
@[simp] theorem roofPhase_normalizeRoof_fractionalSlope_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (σ : ℝ)
    (n : ℕ) :
    roofPhase (normalizeRoof β) (fractionalRoofSlope β σ) n =
      roofPhase β σ n := by
  have hNat := U.eq_linear_add_normalizeRoof n
  have hReal :
      (β n : ℝ) =
        (n : ℝ) * (β 1 : ℝ) + (normalizeRoof β n : ℝ) := by
    exact_mod_cast hNat
  unfold roofPhase fractionalRoofSlope
  rw [hReal]
  ring

/--
正規化 phase を直接使うための薄い表記。
-/
def fractionalRoofPhase
    (β : ℕ → ℕ)
    (σ : ℝ)
    (n : ℕ) : ℝ :=
  roofPhase (normalizeRoof β) (fractionalRoofSlope β σ) n

/--
unit-carry roof では fractional phase は direct phase そのもの。
-/
@[simp] theorem fractionalRoofPhase_eq_roofPhase
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (σ : ℝ)
    (n : ℕ) :
    fractionalRoofPhase β σ n = roofPhase β σ n := by
  unfold fractionalRoofPhase
  exact roofPhase_normalizeRoof_fractionalSlope_eq U σ n

/--
irrationality は整数 anchor を引いても失われない。
-/
theorem fractionalRoofSlope_irrational
    {β : ℕ → ℕ}
    {σ : ℝ}
    (hIrr : Irrational σ) :
    Irrational (fractionalRoofSlope β σ) := by
  unfold fractionalRoofSlope
  exact (irrational_sub_natCast_iff).2 hIrr

/--
roof slope の fractional part は常に閉区間 `[0,1]` に入る。
-/
theorem fractionalRoofSlope_mem_unitInterval
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ) :
    0 ≤ fractionalRoofSlope β σ ∧
      fractionalRoofSlope β σ ≤ 1 := by
  simpa [fractionalRoofSlope] using normalizedSlope_mem_unitInterval S

/--
roof slope が irrational なら端点 `0,1` には乗れないため、fractional slope は strict に `(0,1)`。
-/
theorem fractionalRoofSlope_mem_openUnitInterval_of_irrational
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hIrr : Irrational σ) :
    0 < fractionalRoofSlope β σ ∧
      fractionalRoofSlope β σ < 1 := by
  have hRange := fractionalRoofSlope_mem_unitInterval S
  have hFracIrr : Irrational (fractionalRoofSlope β σ) :=
    fractionalRoofSlope_irrational hIrr
  constructor
  · exact lt_of_le_of_ne hRange.1 (Ne.symm hFracIrr.ne_zero)
  · exact lt_of_le_of_ne hRange.2 hFracIrr.ne_one

/--
irrational roof slope を持つ unit-carry roof は、正規化後に fractional slope の lower mechanical roof になる。
-/
theorem normalizeRoof_isLowerMechanical_fractionalSlope_of_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hIrr : Irrational σ) :
    IsLowerMechanicalRoof
      (normalizeRoof β) (fractionalRoofSlope β σ) := by
  have M : IsLowerMechanicalRoof β σ :=
    U.lowerMechanical_of_irrational_roofSlope S hIrr
  have hNorm :=
    (U.lowerMechanical_normalizeRoof_iff (σ := σ)).1 M
  simpa [fractionalRoofSlope] using hNorm

/--
linear gauge 後の premature phase-wrap roof return 禁止条件は元と exact に同じ。
-/
theorem noPrematurePhaseWrapRoofReturn_linearLift_iff
    (c : ℕ)
    {β : ℕ → ℕ}
    {σ : ℝ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (a r : ℕ) :
    NoPrematurePhaseWrapRoofReturn
        (linearLiftRoof c β) (σ + (c : ℝ)) m
        (linearLiftHeight c height) a r ↔
      NoPrematurePhaseWrapRoofReturn β σ m height a r := by
  constructor
  · intro H j hjPos hjLt hBad
    apply H j hjPos hjLt
    refine ⟨(isProperRoofCut_linearLift_iff
      c β m height (a + j)).2 hBad.1, ?_⟩
    simpa only [roofPhase_linearLiftRoof_eq] using hBad.2
  · intro H j hjPos hjLt hBad
    apply H j hjPos hjLt
    refine ⟨(isProperRoofCut_linearLift_iff
      c β m height (a + j)).1 hBad.1, ?_⟩
    simpa only [roofPhase_linearLiftRoof_eq] using hBad.2

/--
任意 block length 列上の phase threshold compatibility は linear gauge で exact に不変。
-/
theorem phaseThresholdCompatibleFrom_linearLift_iff
    (c : ℕ)
    {β : ℕ → ℕ}
    {σ : ℝ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      PhaseThresholdCompatibleFrom
          (linearLiftRoof c β) (σ + (c : ℝ)) m
          (linearLiftHeight c height) a rs ↔
        PhaseThresholdCompatibleFrom β σ m height a rs
  | _a, [] => by
      simp [PhaseThresholdCompatibleFrom]
  | a, [r] => by
      simp only [PhaseThresholdCompatibleFrom]
      rw [noPrematurePhaseWrapRoofReturn_linearLift_iff c a r]
      simp only [roofPhase_linearLiftRoof_eq]
  | a, r :: s :: rs => by
      simp only [PhaseThresholdCompatibleFrom]
      rw [noPrematurePhaseWrapRoofReturn_linearLift_iff c a r]
      exact and_congr Iff.rfl
        (phaseThresholdCompatibleFrom_linearLift_iff
          c (a + r) (s :: rs))

/--
canonical phase threshold law も record partition と phase の両不変性から exact に gauge 不変。
-/
theorem canonicalPhaseThresholdCompatible_linearLift_iff
    (c : ℕ)
    {β : ℕ → ℕ}
    {σ : ℝ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalPhaseThresholdCompatible
        (linearLiftRoof c β) (σ + (c : ℝ)) m
        (linearLiftHeight c height) ↔
      CanonicalPhaseThresholdCompatible β σ m height := by
  unfold CanonicalPhaseThresholdCompatible
  rw [canonicalRecordLengths_linearLift_eq c]
  exact phaseThresholdCompatibleFrom_linearLift_iff
    c canonicalAnchor (canonicalRecordLengths β m height)

namespace RecordFerrers

/--
標準 RecordFerrers `β(1)=1` では fractional slope は単に `σ-1`。
-/
theorem fractionalRoofSlope_eq_sub_one
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (σ : ℝ) :
    fractionalRoofSlope β σ = σ - 1 := by
  unfold fractionalRoofSlope
  rw [R.roof_one]
  norm_num

/--
RecordFerrers の direct phase は、正規化屋根を `σ-1` で読む phase と exact に同じ。
-/
theorem normalizedRoofPhase_eq_directPhase
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (σ : ℝ)
    (n : ℕ) :
    roofPhase (normalizeRoof β) (σ - 1) n =
      roofPhase β σ n := by
  have h := roofPhase_normalizeRoof_fractionalSlope_eq R.unitCarry σ n
  rw [R.fractionalRoofSlope_eq_sub_one σ] at h
  exact h

/--
RecordFerrers の irrational direct roof slope `σ` から得る真の回転パラメータ `σ-1` は
irrational かつ strict に `(0,1)` に入る。
-/
theorem fractionalSlope_data_of_irrationalRoofSlope
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hIrr : Irrational σ) :
    Irrational (σ - 1) ∧
      0 < σ - 1 ∧
      σ - 1 < 1 := by
  have hIrrFrac := fractionalRoofSlope_irrational
    (β := β) hIrr
  have hRange := fractionalRoofSlope_mem_openUnitInterval_of_irrational
    S hIrr
  rw [R.fractionalRoofSlope_eq_sub_one σ] at hIrrFrac hRange
  exact ⟨hIrrFrac, hRange.1, hRange.2⟩

/--
RecordFerrers の irrational direct roof slope を正規化すると、`σ-1` の lower mechanical roof になる。
-/
theorem normalizeRoof_isLowerMechanical_sub_one_of_irrationalSlope
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hIrr : Irrational σ) :
    IsLowerMechanicalRoof (normalizeRoof β) (σ - 1) := by
  have h := normalizeRoof_isLowerMechanical_fractionalSlope_of_irrational
    R.unitCarry S hIrr
  rw [R.fractionalRoofSlope_eq_sub_one σ] at h
  exact h

/--
RecordFerrers の canonical phase threshold law は、整数 linear gauge と slope の同時 shift に依存しない。

完成 RecordFerrers を lift すると標準条件 `β(1)=1` は失われるが、
本質的 phase threshold law はそのまま残ることを明示する。
-/
theorem phaseThresholdCompatible_linearLift
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (c : ℕ) :
    CanonicalPhaseThresholdCompatible
      (linearLiftRoof c β) (σ + (c : ℝ)) m
      (linearLiftHeight c R.height) := by
  have P : CanonicalPhaseThresholdCompatible β σ m R.height :=
    R.phaseThresholdCompatible M
  exact
    (canonicalPhaseThresholdCompatible_linearLift_iff
      c).2 P

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
