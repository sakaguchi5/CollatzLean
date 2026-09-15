import CollatzLean.Collatz3.Analysis.IrrationalRotationCesaro
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Collatz3 Analysis: 無理回転 Weyl–Cesàro の実数値版

前段の複素値連続関数版を `ℝ → ℂ` の標準埋め込みで実数値へ降ろす。
このファイルも Collatz 固有の定義を import しない。

Lemma 41 型の observable は実数値なので、次段で「1点不連続だが Riemann 可積分」な関数へ
sandwich で拡張するときの入口としてこの版を用意する。
-/

namespace Collatz3
namespace Analysis

open Filter MeasureTheory
open scoped Topology BigOperators

variable {T : ℝ}

/-- 実数値関数の回転軌道 Cesàro 平均。 -/
noncomputable def rotationCesaroReal
    (a x : AddCircle T)
    (f : AddCircle T → ℝ)
    (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, f (x + k • a)

/-- 実数値連続関数を点ごとに `ℂ` へ埋め込んだ連続関数。 -/
noncomputable def complexifyContinuous
    (f : C(AddCircle T, ℝ)) :
    C(AddCircle T, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp] theorem complexifyContinuous_apply
    (f : C(AddCircle T, ℝ))
    (y : AddCircle T) :
    complexifyContinuous f y = (f y : ℂ) :=
  rfl

/-- 実数 Cesàro 平均を複素数へ埋めると、複素化した observable の Cesàro 平均そのもの。 -/
theorem ofReal_rotationCesaroReal
    (a x : AddCircle T)
    (f : C(AddCircle T, ℝ))
    (N : ℕ) :
    ((rotationCesaroReal a x f N : ℝ) : ℂ) =
      rotationCesaro a x (complexifyContinuous f) N := by
  simp [rotationCesaroReal, rotationCesaro, complexifyContinuous]

variable {T : ℝ} [Fact (0 < T)]

/-- 複素化した連続関数の Haar 平均は、実 Haar 平均の標準複素埋め込み。 -/
theorem circleMean_complexifyContinuous
    (f : C(AddCircle T, ℝ)) :
    circleMean (complexifyContinuous f) =
      ((∫ y, f y ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
  simpa [circleMean, complexifyContinuous] using
    (integral_complex_ofReal
      (μ := AddCircle.haarAddCircle)
      (f := fun y : AddCircle T => f y))

/--
**実数値連続関数版 Weyl–Cesàro 定理。**

無限位数回転では任意の実数値連続 observable の軌道平均が Haar 平均へ収束する。
-/
theorem tendsto_rotationCesaroReal_continuous
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    (f : C(AddCircle T, ℝ)) :
    Tendsto
      (fun N => rotationCesaroReal a x f N)
      atTop
      (𝓝 (∫ y, f y ∂AddCircle.haarAddCircle)) := by
  rw [← Filter.tendsto_ofReal_iff]
  have h := tendsto_rotationCesaro_continuous ha x (complexifyContinuous f)
  rw [circleMean_complexifyContinuous] at h
  simpa [ofReal_rotationCesaroReal] using h

/-- `α/T` の無理性から得る実数値連続関数版。 -/
theorem tendsto_rotationCesaroReal_continuous_of_irrational_div
    {α : ℝ}
    (hα : Irrational (α / T))
    (x : AddCircle T)
    (f : C(AddCircle T, ℝ)) :
    Tendsto
      (fun N => rotationCesaroReal (α : AddCircle T) x f N)
      atTop
      (𝓝 (∫ y, f y ∂AddCircle.haarAddCircle)) :=
  tendsto_rotationCesaroReal_continuous
    (addOrderOf_coe_eq_zero_of_irrational_div hα) x f

/-- 単位円周上の通常の無理回転に対する実数値連続関数版。 -/
theorem tendsto_unitRotationCesaroReal_continuous
    {α : ℝ}
    (hα : Irrational α)
    (x : AddCircle (1 : ℝ))
    (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto
      (fun N => rotationCesaroReal (α : AddCircle (1 : ℝ)) x f N)
      atTop
      (𝓝 (∫ y, f y ∂AddCircle.haarAddCircle)) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact tendsto_rotationCesaroReal_continuous
    (addOrderOf_unitCircle_coe_eq_zero hα) x f

end Analysis
end Collatz3
