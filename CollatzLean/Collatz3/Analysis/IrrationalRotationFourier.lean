import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Collatz3 Analysis: 無理回転の Fourier 1文字 Cesàro 平均

このファイルは Collatz 固有の定義を一切 import しない。
円周 `AddCircle T` 上の回転と Fourier 文字だけを扱う。

証明の核は、非零 Fourier mode `m` に対し

`fourier m (x + k • a) = fourier m x * (fourier m a)^k`

と書き、有限和を幾何級数へ落とすことである。
回転元 `a` が無限加法位数なら `m ≠ 0` で `fourier m a ≠ 1` なので、
正規化幾何級数は `N → ∞` で `0` に収束する。

ここでは Weyl の一般連続関数定理はまだ使わない。
Fourier 1文字の exact finite formula と極限だけを閉じる。
-/

namespace Collatz3
namespace Analysis

open Filter Function Set
open scoped Topology BigOperators
open AddCircle

variable {T : ℝ}

/--
回転軌道 `x, x+a, x+2a, ...` 上の有限 Cesàro 平均。
`N = 0` では mathlib の逆元規約により `0` になる。
-/
noncomputable def rotationCesaro
    (a x : AddCircle T)
    (f : AddCircle T → ℂ)
    (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, f (x + k • a)

/-- Cesàro 平均は被積分関数の和に関して加法的。 -/
theorem rotationCesaro_add
    (a x : AddCircle T)
    (f g : AddCircle T → ℂ)
    (N : ℕ) :
    rotationCesaro a x (fun y => f y + g y) N =
      rotationCesaro a x f N + rotationCesaro a x g N := by
  simp [rotationCesaro, Finset.sum_add_distrib, mul_add]

/-- Cesàro 平均は複素スカラー倍を外へ出せる。 -/
theorem rotationCesaro_const_mul
    (a x : AddCircle T)
    (c : ℂ)
    (f : AddCircle T → ℂ)
    (N : ℕ) :
    rotationCesaro a x (fun y => c * f y) N =
      c * rotationCesaro a x f N := by
  simp [rotationCesaro, Finset.mul_sum]
  ring_nf

/-- Fourier 文字は円周加法を複素乗法へ送る。 -/
theorem fourier_add_point
    (m : ℤ)
    (x y : AddCircle T) :
    fourier m (x + y) = fourier m x * fourier m y := by
  simp [fourier_apply, toCircle_add, Circle.coe_mul]

/-- 自然数倍上の Fourier 文字は通常の自然数冪になる。 -/
theorem fourier_nsmul_point
    (m : ℤ)
    (a : AddCircle T)
    (n : ℕ) :
    fourier m (n • a) = (fourier m a) ^ n := by
  induction n with
  | zero => simp only [zero_nsmul, fourier_apply, smul_zero,
                      toCircle_zero, Circle.coe_one, pow_zero]
  | succ n ih =>
      rw [succ_nsmul, fourier_add_point, ih, pow_succ]

/-- 回転軌道上の Fourier 文字の exact 幾何級数形。 -/
theorem fourier_rotation_orbit
    (m : ℤ)
    (a x : AddCircle T)
    (n : ℕ) :
    fourier m (x + n • a) =
      fourier m x * (fourier m a) ^ n := by
  rw [fourier_add_point, fourier_nsmul_point]

/-- 任意の Fourier 文字の各点での複素絶対値は `1`。 -/
theorem fourier_point_norm
    (m : ℤ)
    (x : AddCircle T) :
    ‖fourier m x‖ = 1 := by
  simp only [fourier_apply, Circle.norm_coe]

/-- 正規化幾何級数 `N⁻¹ Σ z^k`。 -/
noncomputable def normalizedGeomCesaro
    (z : ℂ)
    (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, z ^ k

/-- Fourier mode の Cesàro 平均を正規化幾何級数へ exact に因数分解する。 -/
theorem rotationCesaro_fourier_eq
    (a x : AddCircle T)
    (m : ℤ)
    (N : ℕ) :
    rotationCesaro a x (fourier m) N =
      fourier m x * normalizedGeomCesaro (fourier m a) N := by
  simp only [rotationCesaro, normalizedGeomCesaro, fourier_rotation_orbit]
  rw [← Finset.mul_sum]
  ring

variable [Fact (0 < T)]

/--
回転元 `a` が無限加法位数なら、非零 Fourier mode は `a` 上で `1` にならない。
これは幾何級数の分母 `fourier m a - 1` が非零であることを供給する。
-/
theorem fourier_ne_one_of_addOrderOf_eq_zero
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    {m : ℤ}
    (hm : m ≠ 0) :
    fourier m a ≠ 1 := by
  intro h
  have hCircle :
      toCircle (m • a : AddCircle T) = (1 : Circle) := by
    apply Subtype.ext
    simpa [fourier_apply] using h
  have hma : m • a = 0 := by
    apply AddCircle.injective_toCircle
      (show T ≠ 0 from ne_of_gt (Fact.out : 0 < T))
    simpa using hCircle
  have hdiv : (addOrderOf a : ℤ) ∣ m :=
    (addOrderOf_dvd_iff_zsmul_eq_zero).2 hma
  have hm0 : m = 0 := by
    simpa [ha] using hdiv
  exact hm hm0

/--
`‖z‖ = 1` かつ `z ≠ 1` なら、正規化幾何級数は `0` へ収束する。

有限公式

`Σ_{k<N} z^k = (z^N - 1)/(z - 1)`

を使い、右辺第2因子が一様有界、第1因子 `N⁻¹` が `0` へ行くことだけで証明する。
-/
theorem tendsto_normalizedGeomCesaro_zero
    {z : ℂ}
    (hzNorm : ‖z‖ = 1)
    (hzOne : z ≠ 1) :
    Tendsto (normalizedGeomCesaro z) atTop (𝓝 0) := by
  have hDenPos : 0 < ‖z - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hzOne)
  have hBound :
      IsBoundedUnder (· ≤ ·) atTop
        ((‖·‖) ∘ fun N : ℕ => (z ^ N - 1) / (z - 1)) := by
    apply Filter.isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall (fun N : ℕ => by
      change ‖(z ^ N - 1) / (z - 1)‖ ≤ 2 / ‖z - 1‖
      rw [norm_div]
      gcongr
      calc
        ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          norm_num [norm_pow, hzNorm])
  have hMul :
      Tendsto
        (fun N : ℕ =>
          (N : ℂ)⁻¹ * ((z ^ N - 1) / (z - 1)))
        atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).zero_mul_isBoundedUnder_le hBound
  refine hMul.congr' (Filter.Eventually.of_forall ?_)
  intro N
  simp only [normalizedGeomCesaro]
  rw [geom_sum_eq hzOne]



/-- 無限位数回転では、非零 Fourier mode の Cesàro 平均は `0` へ収束する。 -/
theorem tendsto_rotationCesaro_fourier_ne_zero
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    {m : ℤ}
    (hm : m ≠ 0) :
    Tendsto
      (fun N => rotationCesaro a x (fourier m) N)
      atTop (𝓝 0) := by
  have hGeom :
      Tendsto (normalizedGeomCesaro (fourier m a)) atTop (𝓝 0) :=
    tendsto_normalizedGeomCesaro_zero
      (fourier_point_norm m a)
      (fourier_ne_one_of_addOrderOf_eq_zero ha hm)
  have hMul := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => fourier m x) atTop (𝓝 (fourier m x))).mul hGeom
  simpa [rotationCesaro_fourier_eq] using hMul

/--
無限位数回転に対する Fourier 1文字版 Weyl 平均。
零 mode は `1`、非零 mode は `0` へ収束する。
-/
theorem tendsto_rotationCesaro_fourier
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    (m : ℤ) :
    Tendsto
      (fun N => rotationCesaro a x (fourier m) N)
      atTop (𝓝 (if m = 0 then 1 else 0)) := by
  by_cases hm : m = 0
  · subst m
    simp only [↓reduceIte]
    refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono ?_)
    intro N hN
    simp [rotationCesaro, hN]
  · simp only [ite_eq_right hm]
    exact tendsto_rotationCesaro_fourier_ne_zero ha x hm

/--
実数 `α` の円周像が無限位数であることを、`α/T` の無理性から得る。
これは `DenseRange` を経由するだけで、測度論や Collatz は使わない。
-/
theorem addOrderOf_coe_eq_zero_of_irrational_div
    {α : ℝ}
    (hα : Irrational (α / T)) :
    addOrderOf (α : AddCircle T) = 0 := by
  apply (AddCircle.denseRange_zsmul_iff).1
  exact (AddCircle.denseRange_zsmul_coe_iff).2 hα

/-- 単位円周では、無理数 `α` 自身が無限位数回転を与える。 -/
theorem addOrderOf_unitCircle_coe_eq_zero
    {α : ℝ}
    (hα : Irrational α) :
    addOrderOf (α : AddCircle (1 : ℝ)) = 0 := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  apply addOrderOf_coe_eq_zero_of_irrational_div
  simpa using hα

end Analysis
end Collatz3
