import CollatzLean.CollatzSecondLayer3.OrderedPeriodicTailExclusion
import CollatzLean.CollatzSecondLayer3.GenericObstructions
import CollatzLean.CollatzFirstLayer.SignedReplay
import CollatzLean.CollatzFirstLayer.DownwardReplay

/-!
# future-minimum windowのfirst deferredと局所二分岐

非有界軌道のfuture-minimumから任意の正長`q`のordered windowを作る。
ordered infinite normalizationは排除済みなので必ずfirst deferredへ到達する。
terminal deferred windowは、canonical quotientが正ならdeep lower replay、
0ならsigned replayの負性からSpecial C3となる。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- future-minimumから始まる正長windowの初期差分。 -/
noncomputable def futureMinimumWindowDifference
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor q : ℕ)
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q) :
    O.WindowDifferenceData anchor q := by
  have hle : O.value anchor ≤ O.value (anchor + q) :=
    hmin (anchor + q) (by omega)
  have hne : O.value anchor ≠ O.value (anchor + q) := by
    apply O.value_ne_of_lt_of_unbounded hU
    omega
  have hlt : O.value anchor < O.value (anchor + q) := by
    omega
  exact O.windowDifferenceData_of_lt hlt

/-- future-minimumの正長windowは必ずfirst deferredへ到達する。 -/
noncomputable def futureMinimumFirstDeferredData
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor q : ℕ)
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q) :
    O.FiniteCaptureNormalizationData
      (futureMinimumWindowDifference O hU anchor q hmin hq) := by
  let D₀ := futureMinimumWindowDifference O hU anchor q hmin hq
  let outcome :=
    Classical.choice
      (OddOrbit.captureNormalizationFromWindowOutcome_nonempty D₀)
  cases outcome with
  | firstDeferred F => exact F
  | eventuallySynchronized I =>
      exact False.elim (OddOrbit.InfiniteCaptureNormalizationData.impossible_of_length_pos I hq)

/-- future-minimum windowのfirst deferred位置。 -/
noncomputable def futureMinimumTerminalStart
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor q : ℕ)
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q) : ℕ :=
  anchor +
    (futureMinimumFirstDeferredData O hU anchor q hmin hq).terminalTime

/--
任意のdeferred windowはdeep lower replayまたはSpecial C3へ落ちる。
-/
theorem deferredWindow_generic_dichotomy
    {O : OddOrbit} {i q : ℕ}
    (E : O.DeferredWindowAt i q)
    (hq : 0 < q) :
    Nonempty (GenericDeepLowerReplayAt O i q) ∨
      Nonempty (SpecialC3At O i q) := by
  let P : O.PreparedWindowPacket i q :=
    { toWindowDifferenceData := E.toWindowDifferenceData
      length_pos := hq
      depth_le_nextExponent := by
        rw [E.deferred] }
  let C := P.replayCoordinate
  by_cases hzero : C.quotient = 0
  · have hstart :
        O.value i = canonicalStart (O.segmentWord i q) := by
      exact C.start_eq_canonical_of_quotient_eq_zero hzero
    have hend :
        O.value (i + q) = canonicalEnd (O.segmentWord i q) := by
      have h := C.finish_eq
      rw [hzero] at h
      simpa using h
    have hrun₀ := P.run
    rw [hstart, hend] at hrun₀
    have hrun :
        Runs
          (O.segmentWord i q)
          (canonicalStart (O.segmentWord i q))
          (canonicalEnd (O.segmentWord i q)) := by
      exact hrun₀
    have hshadow : predecessorShadow (O.segmentWord i q) < 0 :=
      Runs.predecessorShadow_neg_of_canonical_run hrun
    exact Or.inr
      ⟨specialC3At_of_deferred E hq hstart hend hshadow⟩
  · have hqpos : 0 < C.quotient := Nat.pos_of_ne_zero hzero
    have hlower := C.lowerNaturalRunReplay P.run hqpos
    have hvalid : Valid (O.segmentWord i q) :=
      (O.runs_segment i q).valid
    have hlengthSteps : q ≤ twoSteps (O.segmentWord i q) := by
      have h := oddSteps_le_twoSteps hvalid
      simpa [oddSteps] using h
    have hmodulus :
        2 ^ (q + 1) ≤ residueModulus (O.segmentWord i q) := by
      unfold residueModulus
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact Or.inl
      ⟨{
        lowerReplay := hlower
        modulus_deep := hmodulus
      }⟩

/-- future-minimumの長さ`q` terminalにおける局所二分岐。 -/
theorem futureMinimum_terminal_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor q : ℕ)
    (hmin : O.FutureMinimumAt anchor)
    (hq : 0 < q) :
    Nonempty
        (GenericDeepLowerReplayAt O
          (futureMinimumTerminalStart O hU anchor q hmin hq) q) ∨
      Nonempty
        (SpecialC3At O
          (futureMinimumTerminalStart O hU anchor q hmin hq) q) := by
  have E :
      O.DeferredWindowAt
        (futureMinimumTerminalStart O hU anchor q hmin hq) q := by
    change
      O.DeferredWindowAt
        (anchor +
          (futureMinimumFirstDeferredData O hU anchor q hmin hq).terminalTime) q
    exact
      (futureMinimumFirstDeferredData O hU anchor q hmin hq).terminal
  exact deferredWindow_generic_dichotomy E hq

end CollatzSecondLayer3
