import CollatzLean.Collatz3.Analysis.IrrationalRotationRealCesaro
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Analysis: 連続上下近似による Weyl–Cesàro 拡張

このファイルは Collatz 固有の定義を一切 import しない。

連続関数版 Weyl–Cesàro 定理を、点wise に上下から連続関数で挟め、
かつ Haar 平均を任意に狭く同じ値 `L` の周囲へ挟める実数値 observable へ拡張する。

この条件は Riemann/Darboux 型の薄い interface であり、
有限個の jump discontinuity を持つ bounded observable を後段で扱うための入口になる。
-/

namespace Collatz3
namespace Analysis

open Filter MeasureTheory Set
open scoped Topology BigOperators

variable {T : ℝ}

/-- pointwise order は有限 Cesàro 平均でも保存される。 -/
theorem rotationCesaroReal_mono
    (a x : AddCircle T)
    {f g : AddCircle T → ℝ}
    (hfg : ∀ y, f y ≤ g y)
    (N : ℕ) :
    rotationCesaroReal a x f N ≤ rotationCesaroReal a x g N := by
  unfold rotationCesaroReal
  have hsum :
      (∑ k ∈ Finset.range N, f (x + k • a)) ≤
        ∑ k ∈ Finset.range N, g (x + k • a) := by
    exact Finset.sum_le_sum fun k hk => hfg _
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))

variable {T : ℝ} [Fact (0 < T)]

/--
`f` が Haar 平均候補 `L` を連続関数で上下から任意精度に挟めること。

`l ≤ f ≤ u` を pointwise に要求し、同時に

`L - ε < ∫ l`, `∫ u < L + ε`

を要求する。極限・等分布はこの定義には含めない。
-/
def HasContinuousHaarSandwich
    (f : AddCircle T → ℝ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ l u : C(AddCircle T, ℝ),
      (∀ y, l y ≤ f y) ∧
      (∀ y, f y ≤ u y) ∧
      L - ε < ∫ y, l y ∂AddCircle.haarAddCircle ∧
      ∫ y, u y ∂AddCircle.haarAddCircle < L + ε

/--
**Darboux–Weyl–Cesàro sandwich 定理。**

無限位数回転に対し、`f` が `HasContinuousHaarSandwich f L` を満たすなら、
`f` 自身が連続でなくても軌道 Cesàro 平均は `L` へ収束する。

証明は上下の連続関数に既存の Weyl 定理を適用し、order topology で挟むだけである。
-/
theorem tendsto_rotationCesaroReal_of_continuousHaarSandwich
    {a : AddCircle T}
    (ha : addOrderOf a = 0)
    (x : AddCircle T)
    {f : AddCircle T → ℝ}
    {L : ℝ}
    (hSandwich : HasContinuousHaarSandwich f L) :
    Tendsto
      (fun N => rotationCesaroReal a x f N)
      atTop (𝓝 L) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    let ε : ℝ := (L - b) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨l, u, hlf, hfu, hlMean, huMean⟩ := hSandwich ε hε
    have hbMean : b < ∫ y, l y ∂AddCircle.haarAddCircle := by
      dsimp [ε] at hlMean
      linarith
    have hConv := tendsto_rotationCesaroReal_continuous ha x l
    have hEventually :
        ∀ᶠ N in atTop, b < rotationCesaroReal a x l N :=
      hConv.eventually (Ioi_mem_nhds hbMean)
    filter_upwards [hEventually] with N hN
    exact hN.trans_le (rotationCesaroReal_mono a x hlf N)
  · intro b hb
    let ε : ℝ := (b - L) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨l, u, hlf, hfu, hlMean, huMean⟩ := hSandwich ε hε
    have hMeanB : (∫ y, u y ∂AddCircle.haarAddCircle) < b := by
      dsimp [ε] at huMean
      linarith
    have hConv := tendsto_rotationCesaroReal_continuous ha x u
    have hEventually :
        ∀ᶠ N in atTop, rotationCesaroReal a x u N < b :=
      hConv.eventually (Iio_mem_nhds hMeanB)
    filter_upwards [hEventually] with N hN
    exact (rotationCesaroReal_mono a x hfu N).trans_lt hN

/-- `α/T` が無理なら Darboux sandwich 版 Weyl 定理を適用できる。 -/
theorem tendsto_rotationCesaroReal_of_continuousHaarSandwich_of_irrational_div
    {α : ℝ}
    (hα : Irrational (α / T))
    (x : AddCircle T)
    {f : AddCircle T → ℝ}
    {L : ℝ}
    (hSandwich : HasContinuousHaarSandwich f L) :
    Tendsto
      (fun N => rotationCesaroReal (α : AddCircle T) x f N)
      atTop (𝓝 L) :=
  tendsto_rotationCesaroReal_of_continuousHaarSandwich
    (addOrderOf_coe_eq_zero_of_irrational_div hα) x hSandwich

end Analysis
end Collatz3
