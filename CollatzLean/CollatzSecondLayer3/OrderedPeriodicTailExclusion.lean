import CollatzLean.CollatzWindowCore.NormalizationFromWindow
import CollatzLean.CollatzOrbitCore.PeriodicExponent
import CollatzLean.CollatzOrbitCore.Crossing

/-!
# ordered periodic tailの排除

固定長`q`のordered windowがeventually synchronizedになると、指数tailは`q`周期になる。
一周期語がexpandingなら既存の周期反復排除に反し、contractingなら周期境界の正差が
一周期ごとに狭義減少する。正自然数の無限狭義減少列は存在しないため、
ordered windowから生じるinfinite capture normalizationは不可能である。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 正自然数列は永久に狭義減少できない。 -/
private theorem no_infinite_strict_descent
    (d : ℕ → ℕ)
    (hstep : ∀ k : ℕ, d (k + 1) < d k) :
    False := by
  have hbound : ∀ k : ℕ, d k + k ≤ d 0 := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hs : d (k + 1) + 1 ≤ d k :=
          Nat.succ_le_iff.mpr (hstep k)
        calc
          d (k + 1) + (k + 1)
              = (d (k + 1) + 1) + k := by
                  omega
          _ ≤ d k + k := by
                  exact Nat.add_le_add_right hs k
          _ ≤ d 0 := ih
  have hcontr :=
    hbound (d 0 + 1)
  omega

/--
同じcontracting語を二回続けて実現し、両区間で値が増えるなら、
二回目の増分は一回目の増分より小さい。
-/
private theorem contracting_realization_gap_strict
    {w : ExpWord} {x₀ x₁ x₂ : ℕ}
    (hcontracting : Contracting w)
    (h₀ : Realizes w x₀ x₁)
    (h₁ : Realizes w x₁ x₂)
    (h01 : x₀ < x₁)
    (h12 : x₁ < x₂) :
    x₂ - x₁ < x₁ - x₀ := by
  let A : ℕ := 3 ^ oddSteps w
  let C : ℕ := 2 ^ twoSteps w
  let B : ℕ := affineConst w
  let d₀ : ℕ := x₁ - x₀
  let d₁ : ℕ := x₂ - x₁
  have hx₁ : x₁ = x₀ + d₀ := by
    dsimp [d₀]
    omega
  have hx₂ : x₂ = x₁ + d₁ := by
    dsimp [d₁]
    omega
  have h₀' : C * x₁ = A * x₀ + B := by
    simpa [A, C, B, Realizes] using h₀
  have h₁' : C * x₂ = A * x₁ + B := by
    simpa [A, C, B, Realizes] using h₁
  have hsum :
      (A * x₀ + B) + C * d₁ =
        (A * x₀ + B) + A * d₀ := by
    calc
      (A * x₀ + B) + C * d₁
          = C * x₁ + C * d₁ := by rw [h₀']
      _ = C * (x₁ + d₁) := by ring
      _ = C * x₂ := by rw [← hx₂]
      _ = A * x₁ + B := h₁'
      _ = A * (x₀ + d₀) + B := by rw [hx₁]
      _ = (A * x₀ + B) + A * d₀ := by ring
  have hrec : C * d₁ = A * d₀ :=
    Nat.add_left_cancel hsum
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    exact Nat.sub_pos_of_lt h01
  have hAC : A < C := by
    simpa [A, C, Contracting] using hcontracting
  have hmul : C * d₁ < C * d₀ := by
    calc
      C * d₁ = A * d₀ := hrec
      _ < C * d₀ := (Nat.mul_lt_mul_right hd₀).2 hAC
  have hCpos : 0 < C := by
    dsimp [C]
    exact Nat.pow_pos (by omega)
  have hd : d₁ < d₀ :=
    (Nat.mul_lt_mul_left hCpos).mp hmul
  simpa [d₀, d₁] using hd

namespace OddOrbit.InfiniteCaptureNormalizationData

/-- eventual synchronization開始後では指数列はwindow長`q`を周期に持つ。 -/
theorem exponent_period_of_eventualSynchronization
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (I : O.InfiniteCaptureNormalizationData D₀) :
    ∀ t : ℕ,
      O.exponent
          (start + I.synchronizationStart + t + q) =
        O.exponent
          (start + I.synchronizationStart + t) := by
  intro t
  have S :=
    I.eventuallySynchronized
      (I.synchronizationStart + t)
      (by omega)
  simpa [
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using S.upperExponent_eq_lower

/--
正長ordered windowから生じるinfinite capture normalizationは存在しない。
-/
theorem impossible_of_length_pos
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (I : O.InfiniteCaptureNormalizationData D₀)
    (hq : 0 < q) :
    False := by
  let s : ℕ := start + I.synchronizationStart
  let w : ExpWord := O.segmentWord s q
  have hperiod :
      ∀ t : ℕ,
        O.exponent (s + t + q) = O.exponent (s + t) := by
    intro t
    simpa [s, Nat.add_assoc] using
      exponent_period_of_eventualSynchronization I t
  have hvalid : Valid w := by
    simpa [w] using (O.runs_segment s q).valid
  have hne : w ≠ [] := by
    intro hw
    have hlen := congrArg List.length hw
    have hqzero : q = 0 := by
      simpa [w] using hlen
    omega
  rcases expanding_or_contracting_of_valid_nonempty hvalid hne with
    hexpanding | hcontracting
  · exact
      O.no_expanding_periodic_exponent_tail
        hperiod
        (by simpa [w] using hexpanding)
  · let x : ℕ → ℕ := fun k => O.value (s + k * q)
    let d : ℕ → ℕ := fun k => x (k + 1) - x k
    have hxlt : ∀ k : ℕ, x k < x (k + 1) := by
      intro k
      let D := I.difference (I.synchronizationStart + k * q)
      have hv := D.value_lt
      dsimp [D, x, s]
      simpa [
        Nat.succ_mul,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ] using hv
    have hreal : ∀ k : ℕ, Realizes w (x k) (x (k + 1)) := by
      intro k
      have hr := O.realizes_segment (s + k * q) q
      have hw : O.segmentWord (s + k * q) q = w := by
        simpa [w] using O.segmentWord_mul_period_eq hperiod k
      rw [hw] at hr
      simpa [
        x,
        Nat.succ_mul,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ] using hr
    have hdesc : ∀ k : ℕ, d (k + 1) < d k := by
      intro k
      have hg :=
        contracting_realization_gap_strict
          hcontracting
          (hreal k)
          (hreal (k + 1))
          (hxlt k)
          (hxlt (k + 1))
      simpa [d] using hg
    exact no_infinite_strict_descent d hdesc

end OddOrbit.InfiniteCaptureNormalizationData
end CollatzSecondLayer3
