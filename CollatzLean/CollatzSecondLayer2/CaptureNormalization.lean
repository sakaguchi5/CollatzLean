import CollatzLean.CollatzSecondLayer2.CaptureWindow
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Order.Monotone.Basic


/-!
# capture normalization trajectory

ordered q-windowを一段ずつfirst-carry分類し、
captureではwindow総指数が下降し、synchronizedでは保存される軌道をまとめる。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 任意の正自然数は2冪と奇数部分へ完全分解できる。 -/
theorem exists_exactTwoFactor_of_pos :
    ∀ n : ℕ, 0 < n →
      ∃ d u : ℕ, ExactTwoFactor n d u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      obtain ⟨m, heven | hodd⟩ := n.even_or_odd'
      · have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        obtain ⟨d, u, hfac, hu⟩ := ih m hmlt hmpos
        refine ⟨d + 1, u, ?_, hu⟩
        rw [heven, hfac, pow_succ]
        ring
      · exact ⟨0, n, by simp, ⟨m, hodd⟩⟩

namespace OddOrbit

/-- 二つの軌道値が正順序ならwindow差分データを構成できる。 -/
noncomputable def windowDifferenceData_of_lt
    (O : OddOrbit) {i q : ℕ}
    (hlt : O.value i < O.value (i + q)) :
    O.WindowDifferenceData i q := by
  classical
  let delta := O.value (i + q) - O.value i
  have hdelta : 0 < delta := by
    dsimp [delta]
    omega
  let hex := exists_exactTwoFactor_of_pos delta hdelta
  let d := Classical.choose hex
  let hexu := Classical.choose_spec hex
  let u := Classical.choose hexu
  have hfac : ExactTwoFactor delta d u :=
    Classical.choose_spec hexu
  refine
    { depth := d
      oddPart := u
      difference := ?_
      oddPart_odd := hfac.2 }
  have hfactor := hfac.1
  dsimp [delta] at hfactor
  omega

/-- normalization中の一段。 -/
inductive CaptureNormalizationStep
    (O : OddOrbit) (i q : ℕ) : Type
  | captured (data : O.CapturedWindowAt i q)
  | synchronized (data : O.SynchronizedWindowAt i q)
  | deferred (data : O.DeferredWindowAt i q)

/-- ordered q-windowが全時刻で存在する無限normalization軌道。 -/
structure CaptureNormalizationTrajectory
    (O : OddOrbit) (start q : ℕ) where
  length_pos : 0 < q
  difference : ∀ t : ℕ, O.WindowDifferenceData (start + t) q
  outcome : ∀ t : ℕ, CaptureNormalizationStep O (start + t) q

/-- 最初のdeferred時刻を持つ有限normalization。 -/
structure FirstDeferredNormalizationData
    {O : OddOrbit} {start q : ℕ}
    (T : CaptureNormalizationTrajectory O start q) where
  terminalTime : ℕ
  before : ∀ t : ℕ, t < terminalTime →
    Nonempty
      (O.CapturedWindowAt (start + t) q ⊕
       O.SynchronizedWindowAt (start + t) q)
  terminal : O.DeferredWindowAt (start + terminalTime) q

/-- ある時刻以後の全windowがsynchronized。 -/
structure EventuallySynchronizedNormalizationData
    {O : OddOrbit} {start q : ℕ}
    (T : CaptureNormalizationTrajectory O start q) where
  synchronizationStart : ℕ
  synchronized : ∀ t : ℕ, synchronizationStart ≤ t →
    O.SynchronizedWindowAt (start + t) q

/-- normalization trajectoryの有限deferred / eventual sync分岐。 -/
inductive CaptureNormalizationOutcome
    {O : OddOrbit} {start q : ℕ}
    (T : CaptureNormalizationTrajectory O start q) : Type
  | firstDeferred (data : FirstDeferredNormalizationData T)
  | eventuallySynchronized
      (data : EventuallySynchronizedNormalizationData T)

/-- 正順序が永久に保たれるq-windowからnormalization trajectoryを構成する。 -/
noncomputable def captureNormalizationTrajectory_of_ordered
    (O : OddOrbit) (start q : ℕ)
    (hq : 0 < q)
    (hordered : ∀ t : ℕ,
      O.value (start + t) < O.value (start + t + q)) :
    O.CaptureNormalizationTrajectory start q where
  length_pos := hq

  difference := fun t => by
    have hlt :
        O.value (start + t) <
          O.value ((start + t) + q) := by
      simpa [Nat.add_assoc] using hordered t
    exact O.windowDifferenceData_of_lt
      (i := start + t)
      (q := q)
      hlt

  outcome := fun t => by
    have hlt :
        O.value (start + t) <
          O.value ((start + t) + q) := by
      simpa [Nat.add_assoc] using hordered t
    let D : O.WindowDifferenceData (start + t) q :=
      O.windowDifferenceData_of_lt
        (i := start + t)
        (q := q)
        hlt
    cases O.windowCarryOutcome D with
    | captured C =>
        exact CaptureNormalizationStep.captured C
    | synchronized S =>
        exact CaptureNormalizationStep.synchronized S
    | deferred E =>
        exact CaptureNormalizationStep.deferred E

/-- 一段非増加な自然数列は最終的に一定。 -/
theorem nat_sequence_eventually_constant_of_succ_le
    (a : ℕ → ℕ)
    (hstep : ∀ t : ℕ, a (t + 1) ≤ a t) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → a t = a N := by
  classical
  let hex : ∃ v : ℕ, ∃ t : ℕ, a t = v := ⟨a 0, 0, rfl⟩
  let m := Nat.find hex
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hantitone : Antitone a := antitone_nat_of_succ_le hstep
  refine ⟨N, ?_⟩
  intro t ht
  have hle : a t ≤ a N := hantitone ht
  have hmin : m ≤ a t := by
    exact Nat.find_min' hex ⟨t, rfl⟩
  have hNm : a N = m := hN
  omega

/-- 任意の無限normalization trajectoryはfirst deferredかeventual sync。 -/
theorem captureNormalizationOutcome_nonempty
    {O : OddOrbit} {start q : ℕ}
    (T : O.CaptureNormalizationTrajectory start q) :
    Nonempty (CaptureNormalizationOutcome T) := by
  classical
  by_cases hdefer :
      ∃ t : ℕ, Nonempty (O.DeferredWindowAt (start + t) q)
  · let t0 := Nat.find hdefer
    have ht0 := Nat.find_spec hdefer
    rcases ht0 with ⟨D0⟩
    refine ⟨CaptureNormalizationOutcome.firstDeferred
      { terminalTime := t0
        before := ?_
        terminal := D0 }⟩
    intro t ht
    have hnot : ¬ Nonempty (O.DeferredWindowAt (start + t) q) := by
      intro hD
      exact Nat.not_lt_of_ge (Nat.find_min' hdefer hD) ht
    cases h : T.outcome t with
    | captured C => exact ⟨Sum.inl C⟩
    | synchronized S => exact ⟨Sum.inr S⟩
    | deferred D => exact False.elim (hnot ⟨D⟩)
  · have hHstep : ∀ t : ℕ,
        O.windowTwoSteps (start + (t + 1)) q ≤
          O.windowTwoSteps (start + t) q := by
      intro t
      cases h : T.outcome t with
      | captured C =>
          have hs := C.windowTwoSteps_strict_decrease
          simpa [Nat.add_assoc] using Nat.le_of_lt hs
      | synchronized S =>
          have hs := S.windowTwoSteps_eq
          simpa [Nat.add_assoc] using hs.le
      | deferred D =>
          exact False.elim (hdefer ⟨t, ⟨D⟩⟩)
    obtain ⟨N, hN⟩ :=
      nat_sequence_eventually_constant_of_succ_le
        (fun t => O.windowTwoSteps (start + t) q) hHstep
    refine ⟨CaptureNormalizationOutcome.eventuallySynchronized
      { synchronizationStart := N
        synchronized := ?_ }⟩
    intro t ht
    cases h : T.outcome t with
    | captured C =>
        have hstrict := C.windowTwoSteps_strict_decrease
        have heq0 := hN t ht
        have heq1 := hN (t + 1) (by omega)
        have hindex : start + (t + 1) = (start + t) + 1 := by omega
        rw [← hindex, heq0, heq1] at hstrict
        omega
    | synchronized S => exact S
    | deferred D => exact False.elim (hdefer ⟨t, ⟨D⟩⟩)

end OddOrbit
end CollatzSecondLayer2
