import CollatzLean.CollatzWindowCore.Normalization
import Mathlib.Tactic.Linarith

/-!
# 一つのordered windowからのcapture normalization構成

既存の`captureNormalizationTrajectory_of_ordered`は全時刻の正順序を入力する。
ここではcapture / synchronized carry自身が次の正差windowを生成することを示し、
一つの初期`WindowDifferenceData`だけから

* 最初のdeferredを持つ有限normalization
* deferredが存在せずeventually synchronizedとなる無限normalization

のどちらかを構成する。
-/

namespace CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

namespace CapturedWindowAt

/-- capture直後のupper値の明示式。 -/
theorem upperNext_eq
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.value (i + q + 1) =
      2 ^ (O.exponent i - C.depth) * O.value (i + 1) +
        3 * C.oddPart := by
  let r := O.exponent i - C.depth
  have hr : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt C.captured
  have he : O.exponent i = C.depth + r := by
    dsimp [r]
    omega
  have hlower :
      3 * O.value i + 1 =
        2 ^ (C.depth + r) * O.value (i + 1) := by
    rw [← he]
    exact (O.step i).symm
  have hupper :
      3 * O.value (i + q) + 1 =
        2 ^ C.depth * O.value (i + q + 1) := by
    calc
      3 * O.value (i + q) + 1
          = 2 ^ O.exponent (i + q) * O.value (i + q + 1) := by
              simpa [Nat.add_assoc] using (O.step (i + q)).symm
      _ = 2 ^ C.depth * O.value (i + q + 1) := by
            rw [C.upperExponent_eq_depth]
  have hfactor :
      2 ^ C.depth * O.value (i + q + 1) =
        2 ^ C.depth *
          (2 ^ r * O.value (i + 1) + 3 * C.oddPart) := by
    calc
      2 ^ C.depth * O.value (i + q + 1)
          = 3 * O.value (i + q) + 1 := hupper.symm
      _ = (3 * O.value i + 1) +
            3 * 2 ^ C.depth * C.oddPart := by
              rw [C.difference]
              ring
      _ = 2 ^ (C.depth + r) * O.value (i + 1) +
            3 * 2 ^ C.depth * C.oddPart := by
              rw [hlower]
      _ = 2 ^ C.depth *
            (2 ^ r * O.value (i + 1) + 3 * C.oddPart) := by
              rw [pow_add]
              ring
  have hpow : 0 < 2 ^ C.depth := Nat.pow_pos (by omega)
  exact Nat.mul_left_cancel hpow hfactor

/-- capture直後もq-windowの正順序は保たれる。 -/
theorem next_value_lt
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.value (i + 1) < O.value (i + 1 + q) := by
  have hformula := C.upperNext_eq
  have hr : 0 < O.exponent i - C.depth := by exact Nat.sub_pos_of_lt C.captured
  have hpow : 2 ≤ 2 ^ (O.exponent i - C.depth) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ,
        O.exponent i - C.depth = s + 1 := by
      exact ⟨O.exponent i - C.depth - 1, by omega⟩
    rw [hs, pow_succ]
    have hpos : 1 ≤ 2 ^ s := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    omega
  have hoddPos : 0 < C.oddPart := by
    rcases C.oddPart_odd with ⟨u, hu⟩
    omega
  have hindex : i + 1 + q = i + q + 1 := by omega
  rw [hindex, hformula]
  have hvaluePos : 0 < O.value (i + 1) := by
    rcases O.value_odd (i + 1) with ⟨u, hu⟩
    omega
  nlinarith

/-- capture直後のq-window差分。 -/
noncomputable def nextDifferenceData
    {O : OddOrbit} {i q : ℕ}
    (C : CapturedWindowAt O i q) :
    O.WindowDifferenceData (i + 1) q :=
  O.windowDifferenceData_of_lt C.next_value_lt

end CapturedWindowAt

namespace SynchronizedWindowAt

/-- synchronized carry直後のupper値の明示式。 -/
theorem upperNext_eq
    {O : OddOrbit} {i q : ℕ}
    (S : SynchronizedWindowAt O i q) :
    O.value (i + q + 1) =
      O.value (i + 1) +
        2 ^ (S.depth - O.exponent i) * (3 * S.oddPart) := by
  let e := O.exponent i
  let a := O.value (i + 1)
  have hlower : 3 * O.value i + 1 = 2 ^ e * a := by
    dsimp [e, a]
    exact (O.step i).symm
  let C : SynchronizedCarry
      (O.value i) (O.value (i + q)) S.depth e a S.oddPart :=
    synchronized_carry_of_depth_lt
      S.synchronized S.difference S.oddPart_odd
      hlower (O.value_odd (i + 1))
  have hactual :
      ExactTwoFactor
        (3 * O.value (i + q) + 1)
        (O.exponent (i + q))
        (O.value (i + q + 1)) := by
    refine ⟨?_, O.value_odd _⟩
    simpa [Nat.add_assoc] using (O.step (i + q)).symm
  have hsync :
      ExactTwoFactor
        (3 * O.value (i + q) + 1)
        e C.upperNext :=
    C.upperFactor
  have hexp : O.exponent (i + q) = e :=
    exactTwoFactor_exponent_unique hactual hsync
  have hodd : O.value (i + q + 1) = C.upperNext :=
    exactTwoFactor_oddPart_unique_of_exponent_eq
      hactual hsync hexp
  calc
    O.value (i + q + 1) = C.upperNext := hodd
    _ = a + 2 ^ (S.depth - e) * (3 * S.oddPart) := C.nextDifference
    _ = O.value (i + 1) +
          2 ^ (S.depth - O.exponent i) * (3 * S.oddPart) := by
            rfl

/-- synchronized carry直後もq-windowの正順序は保たれる。 -/
theorem next_value_lt
    {O : OddOrbit} {i q : ℕ}
    (S : SynchronizedWindowAt O i q) :
    O.value (i + 1) < O.value (i + 1 + q) := by
  have hformula := S.upperNext_eq
  have hoddPos : 0 < S.oddPart := by
    rcases S.oddPart_odd with ⟨u, hu⟩
    omega
  have hindex : i + 1 + q = i + q + 1 := by omega
  rw [hindex, hformula]
  apply Nat.lt_add_of_pos_right
  exact Nat.mul_pos
    (Nat.pow_pos (by omega))
    (by omega)

/-- synchronized carry直後のq-window差分。 -/
noncomputable def nextDifferenceData
    {O : OddOrbit} {i q : ℕ}
    (S : SynchronizedWindowAt O i q) :
    O.WindowDifferenceData (i + 1) q :=
  O.windowDifferenceData_of_lt S.next_value_lt

end SynchronizedWindowAt

/-- deferredがまだ現れていない限り、任意の有限時刻まで差分を進められる。 -/
theorem differenceData_at_of_no_deferred_before
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q) :
    ∀ t : ℕ,
      (∀ k : ℕ, k < t →
        ¬ Nonempty (O.DeferredWindowAt (start + k) q)) →
      Nonempty (O.WindowDifferenceData (start + t) q) := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa using (show Nonempty (O.WindowDifferenceData start q) from ⟨D₀⟩)
  | succ t ih =>
      intro hNo
      have hNoBefore : ∀ k : ℕ, k < t →
          ¬ Nonempty (O.DeferredWindowAt (start + k) q) := by
        intro k hk
        exact hNo k (by omega)
      rcases ih hNoBefore with ⟨D⟩
      cases O.windowCarryOutcome D with
      | captured C =>
          have hindex : start + (t + 1) = (start + t) + 1 := by omega
          rw [hindex]
          exact ⟨C.nextDifferenceData⟩
      | synchronized S =>
          have hindex : start + (t + 1) = (start + t) + 1 := by omega
          rw [hindex]
          exact ⟨S.nextDifferenceData⟩
      | deferred E =>
          exact False.elim ((hNo t (by omega)) ⟨E⟩)


/-- 一つの初期差分から最初のdeferredまでを保存する有限normalization。 -/
structure FiniteCaptureNormalizationData
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q) where
  terminalTime : ℕ
  difference : ∀ t : ℕ, t ≤ terminalTime →
    O.WindowDifferenceData (start + t) q
  before : ∀ t : ℕ, t < terminalTime →
    Nonempty
      (O.CapturedWindowAt (start + t) q ⊕
       O.SynchronizedWindowAt (start + t) q)
  terminal : O.DeferredWindowAt (start + terminalTime) q

/-- deferredが一度も現れない無限normalization。 -/
structure InfiniteCaptureNormalizationData
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q) where
  difference : ∀ t : ℕ,
    O.WindowDifferenceData (start + t) q
  nondeferred : ∀ t : ℕ,
    Nonempty
      (O.CapturedWindowAt (start + t) q ⊕
       O.SynchronizedWindowAt (start + t) q)
  synchronizationStart : ℕ
  eventuallySynchronized : ∀ t : ℕ,
    synchronizationStart ≤ t →
    O.SynchronizedWindowAt (start + t) q

/-- 初期ordered windowのfinite deferred / infinite eventual sync分岐。 -/
inductive CaptureNormalizationFromWindowOutcome
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q) : Type
  | firstDeferred
      (data : FiniteCaptureNormalizationData D₀)
  | eventuallySynchronized
      (data : InfiniteCaptureNormalizationData D₀)

/-- deferredが存在する場合、最初のdeferredまでの有限normalizationを構成する。 -/
noncomputable def finiteCaptureNormalizationData_of_exists_deferred
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q)
    (hDeferred : ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q)) :
    FiniteCaptureNormalizationData D₀ := by
  classical
  let T := Nat.find hDeferred
  have hT := Nat.find_spec hDeferred
  refine
    { terminalTime := T
      difference := ?_
      before := ?_
      terminal := Classical.choice hT }
  · intro t ht
    exact Classical.choice
      (differenceData_at_of_no_deferred_before D₀ t
        (by
          intro k hk hD
          have hmin : T ≤ k := Nat.find_min' hDeferred hD
          omega))
  · intro t ht
    let D : O.WindowDifferenceData (start + t) q :=
      Classical.choice
        (differenceData_at_of_no_deferred_before D₀ t
          (by
            intro k hk hD
            have hmin : T ≤ k := Nat.find_min' hDeferred hD
            omega))
    cases O.windowCarryOutcome D with
    | captured C => exact ⟨Sum.inl C⟩
    | synchronized S => exact ⟨Sum.inr S⟩
    | deferred E =>
        have hmin : T ≤ t := Nat.find_min' hDeferred ⟨E⟩
        exact False.elim (by omega)

/-- deferredが存在しなければ全時刻のordered差分を構成できる。 -/
noncomputable def infiniteDifferenceData_of_no_deferred
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q)
    (hNoDeferred : ¬ ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q))
    (t : ℕ) :
    O.WindowDifferenceData (start + t) q :=
  Classical.choice
    (differenceData_at_of_no_deferred_before D₀ t
      (by
        intro k hk hD
        exact hNoDeferred ⟨k, hD⟩))

/-- deferredなしの場合の各時刻はcaptureまたはsynchronized。 -/
theorem capture_or_synchronized_of_no_deferred
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q)
    (hNoDeferred : ¬ ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q))
    (t : ℕ) :
    Nonempty
      (O.CapturedWindowAt (start + t) q ⊕
       O.SynchronizedWindowAt (start + t) q) := by
  let D := infiniteDifferenceData_of_no_deferred D₀ hNoDeferred t
  cases O.windowCarryOutcome D with
  | captured C => exact ⟨Sum.inl C⟩
  | synchronized S => exact ⟨Sum.inr S⟩
  | deferred E => exact False.elim (hNoDeferred ⟨t, ⟨E⟩⟩)

/-- deferredなしならwindow総指数列は一段非増加。 -/
theorem windowTwoSteps_succ_le_of_no_deferred
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q)
    (hNoDeferred : ¬ ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q)) :
    ∀ t : ℕ,
      O.windowTwoSteps (start + (t + 1)) q ≤
        O.windowTwoSteps (start + t) q := by
  intro t
  rcases capture_or_synchronized_of_no_deferred D₀ hNoDeferred t with
    ⟨C | S⟩
  · simpa [Nat.add_assoc] using
      Nat.le_of_lt C.windowTwoSteps_strict_decrease
  · simpa [Nat.add_assoc] using S.windowTwoSteps_eq.le

/-- deferredなしなら、十分後の全windowがsynchronized。 -/
noncomputable def infiniteCaptureNormalizationData_of_no_deferred
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q)
    (hNoDeferred : ¬ ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q)) :
    InfiniteCaptureNormalizationData D₀ := by
  classical
  let a : ℕ → ℕ :=
    fun t => O.windowTwoSteps (start + t) q
  let hexN :=
    nat_sequence_eventually_constant_of_succ_le a
      (windowTwoSteps_succ_le_of_no_deferred D₀ hNoDeferred)
  let N : ℕ :=
    Classical.choose hexN
  have hN :=
    Classical.choose_spec hexN
  refine
    { difference :=
        infiniteDifferenceData_of_no_deferred D₀ hNoDeferred
      nondeferred :=
        capture_or_synchronized_of_no_deferred D₀ hNoDeferred
      synchronizationStart := N
      eventuallySynchronized := ?_ }
  intro t ht
  let outcome :
      O.CapturedWindowAt (start + t) q ⊕
        O.SynchronizedWindowAt (start + t) q :=
    Classical.choice
      (capture_or_synchronized_of_no_deferred
        D₀ hNoDeferred t)
  cases outcome with
  | inl C =>
      have hstrict :=
        C.windowTwoSteps_strict_decrease
      have heq0 :=
        hN t ht
      have heq1 :=
        hN (t + 1) (by omega)
      dsimp [a] at heq0 heq1
      have hindex :
          start + (t + 1) = (start + t) + 1 := by
        omega
      rw [← hindex, heq0, heq1] at hstrict
      have hfalse : False := by
        omega
      exact False.elim hfalse
  | inr S =>
      exact S

/-- 一つの初期ordered windowはfirst deferredまたはeventual syncへ進む。 -/
theorem captureNormalizationFromWindowOutcome_nonempty
    {O : OddOrbit} {start q : ℕ}
    (D₀ : O.WindowDifferenceData start q) :
    Nonempty (CaptureNormalizationFromWindowOutcome D₀) := by
  classical
  by_cases hDeferred : ∃ t : ℕ,
      Nonempty (O.DeferredWindowAt (start + t) q)
  · exact ⟨CaptureNormalizationFromWindowOutcome.firstDeferred
      (finiteCaptureNormalizationData_of_exists_deferred D₀ hDeferred)⟩
  · exact ⟨CaptureNormalizationFromWindowOutcome.eventuallySynchronized
      (infiniteCaptureNormalizationData_of_no_deferred D₀ hDeferred)⟩

end OddOrbit
end CollatzCore
