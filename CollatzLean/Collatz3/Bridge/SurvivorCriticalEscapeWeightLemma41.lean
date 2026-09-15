import CollatzLean.Collatz3.Analysis.UnitCircleOneJumpCesaro
import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeightCesaroReduction
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: 2021 Lemma 41 本体

前段で独立に形式化した

* 連続関数版 Weyl–Cesàro
* continuous Haar sandwich による 1点 jump observable への拡張
* `g(t)=exp(-log 2*t)/3` の unit-circle average

を、既存 `criticalEscapeWeight` の exact floor reduction へ接続する。

結論は

`(1/N) * sum_{m<N} criticalEscapeWeight m -> 1/(6 log 2)`。

この証明は 2021 年論文の real completion / 2進 completion の同一視を一切使わない。
必要なのは finite Beatty floor identity と irrational rotation だけである。
-/

namespace Collatz3
namespace Bridge

open Filter
open scoped Topology BigOperators Real

local instance unitCirclePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- `log₂ 3` の略記を使わず、そのまま profile へ接続する exact identity。 -/
theorem criticalEscapeWeight_eq_lemma41Profile_fract
    (m : ℕ) :
    criticalEscapeWeight m =
      Analysis.lemma41Profile (Int.fract ((m : ℝ) * Real.logb 2 3)) := by
  let «λ» : ℝ := Real.logb 2 3
  let x : ℝ := (m : ℝ) * «λ»
  have «hλnonneg» : 0 ≤ «λ» := by
    dsimp [«λ»]
    exact Real.logb_nonneg (by norm_num) (by norm_num)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hβNat :
      Critical.beattyIndex m = ⌊x⌋₊ := by
    simpa [x, «λ»] using beattyIndex_eq_natFloor_logb_two_three m
  have hβFloor :
      (Critical.beattyIndex m : ℝ) = (⌊x⌋ : ℤ) := by
    have hs := (Nat.floor_eq_iff hxnonneg).1 hβNat.symm
    have hi : ⌊x⌋ = (Critical.beattyIndex m : ℤ) := by
      apply (Int.floor_eq_iff).2
      constructor
      · simpa using hs.1
      · simpa using hs.2
    exact_mod_cast hi.symm
  have hSub :
      (Critical.beattyIndex m : ℝ) - x = -Int.fract x := by
    have hf := Int.floor_add_fract x
    rw [← hβFloor] at hf
    linarith
  have hTwoLog : (2 : ℝ) ^ «λ» = 3 := by
    dsimp [«λ»]
    simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, Real.rpow_logb]
  have hThreePow :
      (3 : ℝ) ^ m = (2 : ℝ) ^ x := by
    calc
      (3 : ℝ) ^ m = ((2 : ℝ) ^ «λ») ^ m := by rw [hTwoLog]
      _ = ((2 : ℝ) ^ «λ») ^ (m : ℝ) := by rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ («λ» * (m : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ x := by
        congr 1
        dsimp [x]
        ring
  unfold criticalEscapeWeight Analysis.lemma41Profile
  rw [pow_succ]
  have hsplit :
      (2 : ℝ) ^ Critical.beattyIndex m /
          ((3 : ℝ) ^ m * 3) =
        (1 / 3 : ℝ) *
          ((2 : ℝ) ^ Critical.beattyIndex m / (3 : ℝ) ^ m) := by
    field_simp
  rw [hsplit, hThreePow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [hSub, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp [x]
  ring_nf
  rfl

/-- 正の index では `m log₂3` の fractional part は `(0,1)` に入る。 -/
theorem lemma41_fract_mem_Ioc
    {m : ℕ} (hm : 0 < m) :
    Int.fract ((m : ℝ) * Real.logb 2 3) ∈ Set.Ioc (0 : ℝ) 1 := by
  have hIrr : Irrational ((m : ℝ) * Real.logb 2 3) := by
    simpa only [Nat.cast_ofNat] using
      irrational_logb_two_three.natCast_mul (Nat.ne_of_gt hm)
  have hne : Int.fract ((m : ℝ) * Real.logb 2 3) ≠ 0 := by
    rw [Int.fract_ne_zero_iff]
    intro hRange
    rcases hRange with ⟨z, hz⟩
    exact hIrr.ne_int z hz.symm
  exact ⟨
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne),
    le_of_lt (Int.fract_lt_one _)
  ⟩

/-- fractional part は unit circle 上で元の実数と同じ点を表す。 -/
theorem coe_fract_eq_unitCircle
    (x : ℝ) :
    ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
  rw [← Int.floor_add_fract x]
  simp

/-- 正の index では circle observable の回転軌道値と critical weight が exact に一致する。 -/
theorem lemma41CircleObservable_nsmul_eq_criticalEscapeWeight
    {m : ℕ} (hm : 0 < m) :
    Analysis.lemma41CircleObservable
        (m • (Real.logb 2 3 : AddCircle (1 : ℝ))) =
      criticalEscapeWeight m := by
  have hr := lemma41_fract_mem_Ioc hm
  have hr' :
      Int.fract ((m : ℝ) * Real.logb 2 3) ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    simpa using hr
  have hcoe :=
    coe_fract_eq_unitCircle ((m : ℝ) * Real.logb 2 3)
  have hnsmul :
      m • (Real.logb 2 3 : AddCircle (1 : ℝ)) =
        (((m : ℝ) * Real.logb 2 3 : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [QuotientAddGroup.mk_nat_mul]
  rw [hnsmul, ← hcoe]
  unfold Analysis.lemma41CircleObservable
  rw [AddCircle.liftIoc_coe_apply hr']
  exact (criticalEscapeWeight_eq_lemma41Profile_fract m).symm

/-- circle observable の index `0` 値は endpoint convention により `1/6`。 -/
theorem lemma41CircleObservable_zero :
    Analysis.lemma41CircleObservable (0 : AddCircle (1 : ℝ)) = (1 : ℝ) / 6 := by
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) (0 + 1) := by norm_num
  have hcoe : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
  rw [← hcoe]
  unfold Analysis.lemma41CircleObservable
  rw [AddCircle.liftIoc_coe_apply h1]
  exact Analysis.lemma41Profile_one

/-- critical weight の index `0` 値は `1/3`。 -/
theorem criticalEscapeWeight_zero :
    criticalEscapeWeight 0 = (1 : ℝ) / 3 := by
  simp [criticalEscapeWeight]

/--
有限和では circle observable と critical weight の差は index `0` の `-1/6` だけ。
-/
theorem lemma41CircleObservable_sum_eq
    {N : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.range N,
        Analysis.lemma41CircleObservable
          (m • (Real.logb 2 3 : AddCircle (1 : ℝ)))) =
      (∑ m ∈ Finset.range N, criticalEscapeWeight m) - (1 : ℝ) / 6 := by
  classical
  let S := (Finset.range N).erase 0
  have h0 : 0 ∈ Finset.range N := by simpa using hN
  calc
    (∑ m ∈ Finset.range N,
        Analysis.lemma41CircleObservable
          (m • (Real.logb 2 3 : AddCircle (1 : ℝ))))
        = Analysis.lemma41CircleObservable (0 : AddCircle (1 : ℝ)) +
            ∑ m ∈ S,
              Analysis.lemma41CircleObservable
                (m • (Real.logb 2 3 : AddCircle (1 : ℝ))) := by
              rw [← Finset.sum_erase_add _ _ h0]
              simp [S]
              simp [add_comm]
    _ = (1 : ℝ) / 6 + ∑ m ∈ S, criticalEscapeWeight m := by
          rw [lemma41CircleObservable_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro m hmS
          have hm0 : m ≠ 0 := by
            simpa [S] using (Finset.mem_erase.1 hmS).1
          exact lemma41CircleObservable_nsmul_eq_criticalEscapeWeight
            (Nat.pos_of_ne_zero hm0)
    _ = (∑ m ∈ Finset.range N, criticalEscapeWeight m) - (1 : ℝ) / 6 := by
          have hWeight :
              (∑ m ∈ Finset.range N, criticalEscapeWeight m) =
                criticalEscapeWeight 0 + ∑ m ∈ S, criticalEscapeWeight m := by
            rw [← Finset.sum_erase_add _ _ h0]
            simp [S]
            simp [add_comm]
          rw [hWeight, criticalEscapeWeight_zero]
          ring

/--
2021 Lemma 41 本体: `criticalEscapeWeight` の Cesàro 平均は `1/(6 log 2)` へ収束する。
-/
theorem tendsto_criticalEscapeWeight_cesaro :
    Tendsto
      (fun N : ℕ =>
        (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ))
      atTop
      (𝓝 (1 / (6 * Real.log 2))) := by
  have hRot :=
    Analysis.tendsto_lemma41CircleObservable_rotationCesaro
      irrational_logb_two_three (0 : AddCircle (1 : ℝ))
  have hCorr :
      Tendsto (fun N : ℕ => (1 / 6 : ℝ) / (N : ℝ))
        atTop (𝓝 0) := by
    have hInv :
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    have hMul :
        Tendsto
          (fun N : ℕ => (1 / 6 : ℝ) * (N : ℝ)⁻¹)
          atTop
          (𝓝 ((1 / 6 : ℝ) * 0)) := by
      exact tendsto_const_nhds.mul hInv
    simpa [div_eq_mul_inv] using hMul
  have hSumForm :
      ∀ᶠ N : ℕ in atTop,
        (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ) =
          Analysis.rotationCesaroReal
            (Real.logb 2 3 : AddCircle (1 : ℝ))
            (0 : AddCircle (1 : ℝ))
            Analysis.lemma41CircleObservable N +
          (1 / 6 : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    unfold Analysis.rotationCesaroReal
    simp only [zero_add]
    have hsum := lemma41CircleObservable_sum_eq hN
    rw [hsum]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp [hNR]
    ring
  have hAdd := hRot.add hCorr
  have hSumForm' :
      ∀ᶠ N : ℕ in atTop,
        Analysis.rotationCesaroReal
            (Real.logb 2 3 : AddCircle (1 : ℝ))
            (0 : AddCircle (1 : ℝ))
            Analysis.lemma41CircleObservable N +
          (1 / 6 : ℝ) / (N : ℝ) =
        (∑ m ∈ Finset.range N, criticalEscapeWeight m) / (N : ℝ) := by
    filter_upwards [hSumForm] with N hN
    exact hN.symm
  simpa using hAdd.congr' hSumForm'

/-- 2021 論文 Lemma 41 の floor 表示そのものにも直ちに戻せる。 -/
theorem tendsto_lemma41_floor_cesaro :
    Tendsto
      (fun N : ℕ =>
        (∑ m ∈ Finset.range N,
            ((2 : ℝ) ^ ⌊(m : ℝ) * Real.logb 2 3⌋₊ /
              (3 : ℝ) ^ (m + 1))) / (N : ℝ))
      atTop
      (𝓝 (1 / (6 * Real.log 2))) := by
  exact
    (criticalEscapeWeight_cesaro_tendsto_iff_lemma41_floor).1
      tendsto_criticalEscapeWeight_cesaro

end Bridge
end Collatz3
