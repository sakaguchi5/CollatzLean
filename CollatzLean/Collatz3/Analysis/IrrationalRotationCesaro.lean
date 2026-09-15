import CollatzLean.Collatz3.Analysis.IrrationalRotationFourier
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Collatz3 Analysis: 無理回転の連続関数 Weyl–Cesàro 定理

このファイルも Collatz 固有の定義を一切 import しない。
前段の Fourier 1文字版から、Fourier span の稠密性を使って
任意の連続複素値関数へ拡張する。

構造は次の4段だけである。

1. Fourier 1文字では幾何級数で Cesàro 極限を計算する。
2. 極限を持つ連続関数全体が複素部分加群になる。
3. Cesàro 平均作用素は sup norm に関して `1`-Lipschitz、円周平均も `1`-Lipschitz。
   したがって極限を持つ関数全体は閉集合である。
4. Fourier span は一様ノルムで稠密なので、その閉部分加群は全連続関数空間になる。

これは標準的な Weyl 証明の「Fourier 文字 + 一様近似」をそのまま Lean 化したもの。
2021年論文の 2進 completion や Collatz 軌道は一切使わない。
-/

namespace Collatz3
namespace Analysis

open Filter Function Set MeasureTheory
open scoped Topology BigOperators
open AddCircle

variable {T : ℝ}

@[simp] theorem rotationCesaro_continuousMap_add
    (a x : AddCircle T)
    (f g : C(AddCircle T, ℂ))
    (N : ℕ) :
    rotationCesaro a x (f + g) N =
      rotationCesaro a x f N + rotationCesaro a x g N := by
  change
    rotationCesaro a x (fun y => f y + g y) N =
      rotationCesaro a x (fun y => f y) N +
        rotationCesaro a x (fun y => g y) N
  exact rotationCesaro_add a x (fun y => f y) (fun y => g y) N

@[simp] theorem rotationCesaro_continuousMap_smul
    (a x : AddCircle T)
    (c : ℂ)
    (f : C(AddCircle T, ℂ))
    (N : ℕ) :
    rotationCesaro a x (c • f) N =
      c * rotationCesaro a x f N := by
  change
    rotationCesaro a x (fun y => c * f y) N =
      c * rotationCesaro a x (fun y => f y) N
  exact rotationCesaro_const_mul a x c (fun y => f y) N


variable {T : ℝ} [Fact (0 < T)]

/-- 連続複素値関数の正規化 Haar 平均。 -/
noncomputable def circleMean
    (f : C(AddCircle T, ℂ)) : ℂ :=
  ∫ y, f y ∂AddCircle.haarAddCircle

/-- compact circle 上の連続関数は正規化 Haar 測度に関して可積分。 -/
private theorem continuousMap_integrable_haar
    (f : C(AddCircle T, ℂ)) :
    Integrable f AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f)

@[simp] theorem circleMean_zero :
    circleMean (0 : C(AddCircle T, ℂ)) = 0 := by
  simp [circleMean]

@[simp] theorem circleMean_add
    (f g : C(AddCircle T, ℂ)) :
    circleMean (f + g) = circleMean f + circleMean g := by
  simpa [circleMean] using
    integral_add (continuousMap_integrable_haar f) (continuousMap_integrable_haar g)

@[simp] theorem circleMean_smul
    (c : ℂ)
    (f : C(AddCircle T, ℂ)) :
    circleMean (c • f) = c * circleMean f := by
  change (∫ y, c • f y ∂AddCircle.haarAddCircle) =
    c * (∫ y, f y ∂AddCircle.haarAddCircle)
  simpa [smul_eq_mul] using
    (integral_smul c (fun y : AddCircle T => f y))

/-- Fourier 文字の Haar 平均は零 mode だけ `1`、他は `0`。 -/
theorem circleMean_fourier
    (m : ℤ) :
    circleMean (fourier (T := T) m) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (fun q : ℤ → ℂ => q 0)
    (fourierCoeff_fourier (T := T) m)
  by_cases hm : m = 0
  · subst m
    simp only [circleMean, fourier_apply, zero_smul, toCircle_zero,
     Circle.coe_one, integral_const, probReal_univ,one_smul, ↓reduceIte]
  · simpa [circleMean, fourierCoeff, hm] using h

/--
Cesàro 平均作用素は被観測関数の sup norm に関して非拡大的。
この一様な `1`-Lipschitz 性が Fourier span から閉包へ極限を移す鍵になる。
-/
theorem rotationCesaro_sub_norm_le
    (a x : AddCircle T)
    (f g : C(AddCircle T, ℂ))
    (N : ℕ) :
    ‖rotationCesaro a x f N - rotationCesaro a x g N‖ ≤ ‖f - g‖ := by
  by_cases hN : N = 0
  · subst N
    simp [rotationCesaro]
  · have hSum :
        ‖∑ k ∈ Finset.range N,
            (f (x + k • a) - g (x + k • a))‖ ≤
          (N : ℝ) * ‖f - g‖ := by
      calc
        ‖∑ k ∈ Finset.range N,
            (f (x + k • a) - g (x + k • a))‖
            ≤ ∑ k ∈ Finset.range N,
                ‖f (x + k • a) - g (x + k • a)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range N, ‖f - g‖ := by
          gcongr with k hk
          simpa only [ContinuousMap.sub_apply] using
            ContinuousMap.norm_coe_le_norm (f - g) (x + k • a)
        _ = (N : ℝ) * ‖f - g‖ := by simp
    rw [rotationCesaro, rotationCesaro, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [norm_mul]
    calc
      ‖(N : ℂ)⁻¹‖ *
          ‖∑ k ∈ Finset.range N,
              (f (x + k • a) - g (x + k • a))‖
          ≤ ‖(N : ℂ)⁻¹‖ * ((N : ℝ) * ‖f - g‖) := by
        gcongr
      _ = ‖f - g‖ := by
        have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        have hNormInv : ‖(N : ℂ)⁻¹‖ = ((N : ℝ))⁻¹ := by
          simp
        rw [hNormInv]
        calc
          ((N : ℝ))⁻¹ * ((N : ℝ) * ‖f - g‖) =
              (((N : ℝ))⁻¹ * (N : ℝ)) * ‖f - g‖ := by ring
          _ = ‖f - g‖ := by rw [inv_mul_cancel₀ hNR, one_mul]

/-- 各 `N` の Cesàro 平均作用素は同じ Lipschitz 定数 `1` を持つ。 -/
theorem rotationCesaro_lipschitz
    (a x : AddCircle T)
    (N : ℕ) :
    LipschitzWith 1
      (fun f : C(AddCircle T, ℂ) => rotationCesaro a x f N) := by
  apply LipschitzWith.mk_one
  intro f g
  simpa [dist_eq_norm] using
    rotationCesaro_sub_norm_le a x f g N

/-- Haar 平均も sup norm に関して非拡大的。 -/
theorem circleMean_sub_norm_le
    (f g : C(AddCircle T, ℂ)) :
    ‖circleMean f - circleMean g‖ ≤ ‖f - g‖ := by
  rw [circleMean, circleMean,
    ← integral_sub (continuousMap_integrable_haar f) (continuousMap_integrable_haar g)]
  have h := norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (C := ‖f - g‖)
    (Filter.Eventually.of_forall (fun y : AddCircle T => by
      simpa only [ContinuousMap.sub_apply] using
        ContinuousMap.norm_coe_le_norm (f - g) y))
  simpa using h

/-- Haar 平均作用素は `1`-Lipschitz。 -/
theorem circleMean_lipschitz :
    LipschitzWith 1
      (circleMean : C(AddCircle T, ℂ) → ℂ) := by
  apply LipschitzWith.mk_one
  intro f g
  simpa [dist_eq_norm] using circleMean_sub_norm_le f g

/--
固定した無限位数回転と始点に対し、Weyl–Cesàro 極限を持つ連続関数全体。
線形性だけを structure に入れ、閉性は後で導出する。
-/
noncomputable def irrationalRotationConvergentSubmodule
    (a x : AddCircle T) :
    Submodule ℂ C(AddCircle T, ℂ) where
  carrier :=
    {f | Tendsto
      (fun N => rotationCesaro a x f N)
      atTop (𝓝 (circleMean f))}
  zero_mem' := by
    simp only [rotationCesaro, circleMean, mem_ofPred_eq, ContinuousMap.zero_apply,
            Finset.sum_const_zero, mul_zero,integral_zero, tendsto_const_nhds_iff]
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro c f hf
    have h :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul hf
    simpa [smul_eq_mul] using h

/--
極限を持つ関数全体は sup norm で閉じている。
理由は有限 Cesàro 平均が一様に `1`-Lipschitz で、極限 Haar 平均も連続だからである。
-/
theorem irrationalRotationConvergentSubmodule_isClosed
    (a x : AddCircle T) :
    IsClosed
      (irrationalRotationConvergentSubmodule a x :
        Set C(AddCircle T, ℂ)) := by
  change IsClosed
    {f : C(AddCircle T, ℂ) |
      Tendsto (fun N => rotationCesaro a x f N)
        atTop (𝓝 (circleMean f))}
  have hEq :
      UniformEquicontinuous
        (fun N : ℕ =>
          fun f : C(AddCircle T, ℂ) => rotationCesaro a x f N) :=
    LipschitzWith.uniformEquicontinuous
      (fun N : ℕ =>
        fun f : C(AddCircle T, ℂ) => rotationCesaro a x f N)
      1
      (fun N => rotationCesaro_lipschitz a x N)
  exact hEq.equicontinuous.isClosed_setOfPred_tendsto
    circleMean_lipschitz.continuous

/-- 無限位数回転では、すべての Fourier 文字が収束部分加群に入る。 -/
theorem fourier_mem_irrationalRotationConvergentSubmodule
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    (m : ℤ) :
    fourier m ∈ irrationalRotationConvergentSubmodule a x := by
  change Tendsto
    (fun N => rotationCesaro a x (fourier m) N)
    atTop (𝓝 (circleMean (fourier m)))
  rw [circleMean_fourier]
  exact tendsto_rotationCesaro_fourier ha x m

/--
**連続関数版 Weyl–Cesàro 定理。**

円周上の回転元 `a` が無限加法位数なら、任意の始点 `x` と任意の連続複素値関数 `f` について
軌道 Cesàro 平均は正規化 Haar 平均へ収束する。
-/
theorem tendsto_rotationCesaro_continuous
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    (f : C(AddCircle T, ℂ)) :
    Tendsto
      (fun N => rotationCesaro a x f N)
      atTop (𝓝 (circleMean f)) := by
  let S := irrationalRotationConvergentSubmodule a x
  have hRange :
      Set.range (@fourier T) ⊆ (S : Set C(AddCircle T, ℂ)) := by
    rintro _ ⟨m, rfl⟩
    exact fourier_mem_irrationalRotationConvergentSubmodule ha x m
  have hSpan :
      Submodule.span ℂ (Set.range (@fourier T)) ≤ S :=
    Submodule.span_le.2 hRange
  have hClosure :
      (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure ≤ S :=
    (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure_minimal
      hSpan (irrationalRotationConvergentSubmodule_isClosed a x)
  rw [span_fourier_closure_eq_top] at hClosure
  change f ∈ S
  exact hClosure (by simp)

/-- `α/T` が無理数なら、実数 `α` が定める回転に連続関数版 Weyl 定理を適用できる。 -/
theorem tendsto_rotationCesaro_continuous_of_irrational_div
    {α : ℝ}
    (hα : Irrational (α / T))
    (x : AddCircle T)
    (f : C(AddCircle T, ℂ)) :
    Tendsto
      (fun N => rotationCesaro (α : AddCircle T) x f N)
      atTop (𝓝 (circleMean f)) :=
  tendsto_rotationCesaro_continuous
    (addOrderOf_coe_eq_zero_of_irrational_div hα) x f

/-- 単位円周上の通常の無理回転に対する連続関数版 Weyl 定理。 -/
theorem tendsto_unitRotationCesaro_continuous
    {α : ℝ}
    (hα : Irrational α)
    (x : AddCircle (1 : ℝ))
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto
      (fun N => rotationCesaro (α : AddCircle (1 : ℝ)) x f N)
      atTop (𝓝 (circleMean f)) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact tendsto_rotationCesaro_continuous
    (addOrderOf_unitCircle_coe_eq_zero hα) x f

end Analysis
end Collatz3
