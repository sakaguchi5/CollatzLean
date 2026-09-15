import CollatzLean.Collatz3.Analysis.IrrationalRotationDarbouxCesaro
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Analysis: 単位円周上の 1 点 jump observable

2021 Lemma 41 に現れる observable

`g(t) = exp(-log 2 * t) / 3 = 2^(-t) / 3`,  `0 < t ≤ 1`

を単位円周へ `liftIoc` で持ち上げる。
継ぎ目 `0 = 1` で `1/3` と `1/6` の jump が一つだけある。

左端・右端に連続 triangular bump を足し引きして pointwise sandwich を作り、
その Haar 平均差を `O(δ)` で抑える。

このファイルも Collatz 固有の定義を import しない。
-/

namespace Collatz3
namespace Analysis

open Filter MeasureTheory Set intervalIntegral
open scoped Topology BigOperators Real Interval

local instance unitCirclePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Lemma 41 の基本 profile。 -/
noncomputable def lemma41Profile (t : ℝ) : ℝ :=
  Real.exp (- Real.log 2 * t) / 3

/-- profile は連続。 -/
theorem continuous_lemma41Profile :
    Continuous lemma41Profile := by
  unfold lemma41Profile
  fun_prop

@[simp] theorem lemma41Profile_zero : lemma41Profile 0 = (1 : ℝ) / 3 := by
  simp [lemma41Profile]

@[simp] theorem lemma41Profile_one : lemma41Profile 1 = (1 : ℝ) / 6 := by
  unfold lemma41Profile
  rw [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- 単位円周へ `(0,1]` fundamental domain で持ち上げた 1 点 jump observable。 -/
noncomputable def lemma41CircleObservable : AddCircle (1 : ℝ) → ℝ :=
  AddCircle.liftIoc (1 : ℝ) 0 lemma41Profile

/-- 左端 triangular bump。`δ>0` なら常に非負。 -/
noncomputable def lemma41LeftBump (δ t : ℝ) : ℝ :=
  max 0 (1 - t / δ)

/-- 右端 triangular bump。 -/
noncomputable def lemma41RightBump (δ t : ℝ) : ℝ :=
  max 0 (1 - (1 - t) / δ)

/-- lower profile: 左端 jump を `1/6` だけ削って endpoint を一致させる。 -/
noncomputable def lemma41LowerProfile (δ t : ℝ) : ℝ :=
  lemma41Profile t - (1 / 6 : ℝ) * lemma41LeftBump δ t

/-- upper profile: 右端 jump を `1/6` だけ持ち上げて endpoint を一致させる。 -/
noncomputable def lemma41UpperProfile (δ t : ℝ) : ℝ :=
  lemma41Profile t + (1 / 6 : ℝ) * lemma41RightBump δ t

/-- `δ>0` なら left bump は連続。 -/
theorem continuous_lemma41LeftBump {δ : ℝ} :
    Continuous (lemma41LeftBump δ) := by
  unfold lemma41LeftBump
  fun_prop

/-- `δ>0` なら right bump は連続。 -/
theorem continuous_lemma41RightBump {δ : ℝ} :
    Continuous (lemma41RightBump δ) := by
  unfold lemma41RightBump
  fun_prop

/-- lower profile は連続。 -/
theorem continuous_lemma41LowerProfile {δ : ℝ} :
    Continuous (lemma41LowerProfile δ) := by
  unfold lemma41LowerProfile
  exact continuous_lemma41Profile.sub
    (continuous_const.mul (continuous_lemma41LeftBump))

/-- upper profile は連続。 -/
theorem continuous_lemma41UpperProfile {δ : ℝ} :
    Continuous (lemma41UpperProfile δ) := by
  unfold lemma41UpperProfile
  exact continuous_lemma41Profile.add
    (continuous_const.mul (continuous_lemma41RightBump))

/-- `0<δ≤1` なら lower profile の endpoints は一致する。 -/
theorem lemma41LowerProfile_endpoints
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    lemma41LowerProfile δ 0 = lemma41LowerProfile δ 1 := by
  have h1div : 1 ≤ 1 / δ := by
    exact (le_div_iff₀ hδ).2 (by simpa using hδ1)
  have hInv : 1 ≤ δ⁻¹ := by
    simpa [one_div] using h1div
  have hBumpOne : max 0 (1 - δ⁻¹) = 0 := by
    exact max_eq_left (sub_nonpos.mpr hInv)
  simp [lemma41LowerProfile, lemma41LeftBump,hBumpOne]
  norm_num

/-- `0<δ≤1` なら upper profile の endpoints は一致する。 -/
theorem lemma41UpperProfile_endpoints
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    lemma41UpperProfile δ 0 = lemma41UpperProfile δ 1 := by
  have h1div : 1 ≤ 1 / δ := by
    exact (le_div_iff₀ hδ).2 (by simpa using hδ1)
  have hInv : 1 ≤ δ⁻¹ := by
    simpa [one_div] using h1div
  simp [lemma41UpperProfile, lemma41RightBump, hInv]
  norm_num

/-- lower profile は profile 以下。 -/
theorem lemma41LowerProfile_le
    {δ t : ℝ} :
    lemma41LowerProfile δ t ≤ lemma41Profile t := by
  unfold lemma41LowerProfile lemma41LeftBump
  have hb : 0 ≤ max 0 (1 - t / δ) := le_max_left _ _
  nlinarith

/-- profile は upper profile 以下。 -/
theorem lemma41Profile_le_UpperProfile
    {δ t : ℝ} :
    lemma41Profile t ≤ lemma41UpperProfile δ t := by
  unfold lemma41UpperProfile lemma41RightBump
  have hb : 0 ≤ max 0 (1 - (1 - t) / δ) := le_max_left _ _
  nlinarith

/-- profile の unit interval integral。 -/
theorem integral_lemma41Profile :
    (∫ t in (0 : ℝ)..1, lemma41Profile t) =
      1 / (6 * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let F : ℝ → ℝ := fun t =>
    -(1 / (3 * Real.log 2)) * Real.exp (-Real.log 2 * t)
  have hF : ∀ t : ℝ, HasDerivAt F (lemma41Profile t) t := by
    intro t
    have hInner :
        HasDerivAt (fun x : ℝ => -Real.log 2 * x) (-Real.log 2) t := by
      simpa using (hasDerivAt_id t).const_mul (-Real.log 2)
    have hExp :=
      (Real.hasDerivAt_exp (-Real.log 2 * t)).comp t hInner
    have hMul :=
      hExp.const_mul (-(1 / (3 * Real.log 2)))
    have hDerivEq :
        -(1 / (3 * Real.log 2)) *
            (Real.exp (-Real.log 2 * t) * -Real.log 2) =
          lemma41Profile t := by
      unfold lemma41Profile
      field_simp [ne_of_gt hlog]
    rw [← hDerivEq]
    simpa [F, Function.comp_def] using hMul
  have hInt : IntervalIntegrable lemma41Profile volume 0 1 :=
    continuous_lemma41Profile.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hInt]
  dsimp [F]
  rw [mul_zero, Real.exp_zero, mul_one, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  field_simp [ne_of_gt hlog]
  ring

/-- left bump の unit interval integral は高々 `δ`。 -/
theorem integral_lemma41LeftBump_le
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in (0 : ℝ)..1, lemma41LeftBump δ t) ≤ δ := by
  have hCont := continuous_lemma41LeftBump (δ:=δ)
  rw [← integral_add_adjacent_intervals (b := δ)
      (hCont.intervalIntegrable 0 δ) (hCont.intervalIntegrable δ 1)]
  have hLeft : (∫ t in (0 : ℝ)..δ, lemma41LeftBump δ t) ≤ δ := by
    calc
      (∫ t in (0 : ℝ)..δ, lemma41LeftBump δ t)
          ≤ ∫ _t in (0 : ℝ)..δ, (1 : ℝ) := by
            apply intervalIntegral.integral_mono_on hδ.le
            · exact hCont.intervalIntegrable 0 δ
            · exact intervalIntegrable_const
            · intro t ht
              unfold lemma41LeftBump
              rw [max_le_iff]
              constructor
              · norm_num
              · have ht0 : 0 ≤ t := ht.1
                have : 0 ≤ t / δ := div_nonneg ht0 hδ.le
                linarith
      _ = δ := by simp
  have hRight :
      (∫ t in δ..1, lemma41LeftBump δ t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Filter.Eventually.of_forall ?_
    intro t ht
    unfold lemma41LeftBump
    have htδlt : δ < t := by
      simpa [min_eq_left hδ1] using ht.1
    have htδ : δ ≤ t := le_of_lt htδlt
    have hdiv : 1 ≤ t / δ := by
      exact (le_div_iff₀ hδ).2 (by simpa using htδ)
    rw [max_eq_left]
    linarith
  rw [hRight, add_zero]
  exact hLeft

/-- right bump の unit interval integral は高々 `δ`。 -/
theorem integral_lemma41RightBump_le
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in (0 : ℝ)..1, lemma41RightBump δ t) ≤ δ := by
  have hMirror :
      (∫ t in (0 : ℝ)..1, lemma41RightBump δ t) =
        ∫ t in (0 : ℝ)..1, lemma41LeftBump δ t := by
    simpa [lemma41LeftBump, lemma41RightBump] using
      (intervalIntegral.integral_comp_sub_left
        (f := lemma41LeftBump δ)
        (a := (0 : ℝ))
        (b := 1)
        (d := 1))
  rw [hMirror]
  exact integral_lemma41LeftBump_le hδ hδ1

/-- unit circle の normalized Haar integral と unit interval integral の bridge。 -/
theorem integral_haar_liftIoc_unit
    (f : ℝ → ℝ) :
    (∫ y : AddCircle (1 : ℝ), AddCircle.liftIoc (1 : ℝ) 0 f y
        ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, f t := by
  rw [AddCircle.integral_haarAddCircle]
  norm_num
  simpa using (AddCircle.integral_liftIoc_eq_intervalIntegral
    (T := (1 : ℝ)) (t := (0 : ℝ)) (f := f))

/--
Lemma 41 observable は continuous Haar sandwich を持ち、平均値は `1/(6 log 2)`。
-/
theorem lemma41CircleObservable_hasContinuousHaarSandwich :
    HasContinuousHaarSandwich
      lemma41CircleObservable
      (1 / (6 * Real.log 2)) := by
  intro ε hε
  let δ : ℝ := min (1 / 2 : ℝ) (3 * ε)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (mul_pos (by norm_num) hε)
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact (min_le_left _ _).trans (by norm_num)
  have hδne : δ ≠ 0 := ne_of_gt hδ
  let l : C(AddCircle (1 : ℝ), ℝ) :=
    { toFun := AddCircle.liftIoc (1 : ℝ) 0 (lemma41LowerProfile δ)
      continuous_toFun := by
        apply AddCircle.liftIoc_zero_continuous
        · exact lemma41LowerProfile_endpoints hδ hδ1
        · exact (continuous_lemma41LowerProfile).continuousOn }
  let u : C(AddCircle (1 : ℝ), ℝ) :=
    { toFun := AddCircle.liftIoc (1 : ℝ) 0 (lemma41UpperProfile δ)
      continuous_toFun := by
        apply AddCircle.liftIoc_zero_continuous
        · exact lemma41UpperProfile_endpoints hδ hδ1
        · exact (continuous_lemma41UpperProfile).continuousOn }
  have hProfileInt :
      IntervalIntegrable lemma41Profile volume (0 : ℝ) 1 :=
    continuous_lemma41Profile.intervalIntegrable 0 1
  have hLeftScaledInt :
      IntervalIntegrable
        (fun t : ℝ => (1 / 6 : ℝ) * lemma41LeftBump δ t)
        volume (0 : ℝ) 1 := by
    exact
      (continuous_const.mul
        (continuous_lemma41LeftBump (δ := δ))).intervalIntegrable 0 1
  have hRightScaledInt :
      IntervalIntegrable
        (fun t : ℝ => (1 / 6 : ℝ) * lemma41RightBump δ t)
        volume (0 : ℝ) 1 := by
    exact
      (continuous_const.mul
        (continuous_lemma41RightBump (δ := δ))).intervalIntegrable 0 1
  refine ⟨l, u, ?_, ?_, ?_, ?_⟩
  · intro y
    let r := AddCircle.equivIoc (1 : ℝ) 0 y
    change AddCircle.liftIoc (1 : ℝ) 0 (lemma41LowerProfile δ) y ≤
      AddCircle.liftIoc (1 : ℝ) 0 lemma41Profile y
    rw [← (AddCircle.equivIoc (1 : ℝ) 0).symm_apply_apply y]
    change AddCircle.liftIoc (1 : ℝ) 0 (lemma41LowerProfile δ) (↑r : AddCircle (1 : ℝ)) ≤
      AddCircle.liftIoc (1 : ℝ) 0 lemma41Profile (↑r : AddCircle (1 : ℝ))
    rw [AddCircle.liftIoc_coe_apply r.property,
        AddCircle.liftIoc_coe_apply r.property]
    exact lemma41LowerProfile_le
  · intro y
    let r := AddCircle.equivIoc (1 : ℝ) 0 y
    change AddCircle.liftIoc (1 : ℝ) 0 lemma41Profile y ≤
      AddCircle.liftIoc (1 : ℝ) 0 (lemma41UpperProfile δ) y
    rw [← (AddCircle.equivIoc (1 : ℝ) 0).symm_apply_apply y]
    change AddCircle.liftIoc (1 : ℝ) 0 lemma41Profile (↑r : AddCircle (1 : ℝ)) ≤
      AddCircle.liftIoc (1 : ℝ) 0 (lemma41UpperProfile δ) (↑r : AddCircle (1 : ℝ))
    rw [AddCircle.liftIoc_coe_apply r.property,
        AddCircle.liftIoc_coe_apply r.property]
    exact lemma41Profile_le_UpperProfile
  · change
      1 / (6 * Real.log 2) - ε <
        ∫ y : AddCircle (1 : ℝ),
          AddCircle.liftIoc (1 : ℝ) 0 (lemma41LowerProfile δ) y
          ∂AddCircle.haarAddCircle
    rw [integral_haar_liftIoc_unit]
    unfold lemma41LowerProfile
    rw [intervalIntegral.integral_sub hProfileInt hLeftScaledInt,
        intervalIntegral.integral_const_mul,
        integral_lemma41Profile]
    have hb := integral_lemma41LeftBump_le hδ hδ1
    have hδeps : δ / 6 < ε := by
      have hδle : δ ≤ 3 * ε := min_le_right _ _
      nlinarith
    nlinarith
  · change
      (∫ y : AddCircle (1 : ℝ),
          AddCircle.liftIoc (1 : ℝ) 0 (lemma41UpperProfile δ) y
          ∂AddCircle.haarAddCircle) <
        1 / (6 * Real.log 2) + ε
    rw [integral_haar_liftIoc_unit]
    unfold lemma41UpperProfile
    rw [intervalIntegral.integral_add hProfileInt hRightScaledInt,
        intervalIntegral.integral_const_mul,
        integral_lemma41Profile]
    have hb := integral_lemma41RightBump_le hδ hδ1
    have hδeps : δ / 6 < ε := by
      have hδle : δ ≤ 3 * ε := min_le_right _ _
      nlinarith
    nlinarith

/--
単位円周上の無理回転で Lemma 41 observable の Cesàro 平均は `1/(6 log 2)` へ収束する。
-/
theorem tendsto_lemma41CircleObservable_rotationCesaro
    {α : ℝ}
    (hα : Irrational α)
    (x : AddCircle (1 : ℝ)) :
    Tendsto
      (fun N => rotationCesaroReal
        (α : AddCircle (1 : ℝ)) x lemma41CircleObservable N)
      atTop
      (𝓝 (1 / (6 * Real.log 2))) := by
  exact tendsto_rotationCesaroReal_of_continuousHaarSandwich
    (addOrderOf_unitCircle_coe_eq_zero hα)
    x lemma41CircleObservable_hasContinuousHaarSandwich

end Analysis
end Collatz3
