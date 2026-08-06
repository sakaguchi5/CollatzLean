import CollatzLean.CollatzSecondLayer3.FirstCriticalTerminalRefinement
import CollatzLean.CollatzFirstLayer.SignedReplay

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FirstCriticalTransitionTowerData

/-- short positive-shadow terminalはsigned replayの符号保存に反する。 -/
theorem shortPositiveShadowTerminalAt_impossible
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (S : ShortPositiveShadowTerminalAt R j) :
    False := by
  let P := R.terminalPacket j
  let C := P.replayCoordinate
  have hq0 : C.quotient = 0 := by
    simpa [C, P, terminalReplayQuotient] using S.canonicalBoundary
  have hstart :
      O.value (R.terminalStart j) =
        canonicalStart (R.terminalWord j) := by
    simpa [C, P, terminalWord] using
      C.start_eq_canonical_of_quotient_eq_zero hq0
  have hend :
      O.value (R.terminalStart j + R.windowLength j) =
        canonicalEnd (R.terminalWord j) := by
    have h := C.finish_eq
    rw [hq0] at h
    simpa [terminalWord] using h
  have hrun0 := P.run
  rw [hstart, hend] at hrun0
  have hrun :
      Runs
        (R.terminalWord j)
        (canonicalStart (R.terminalWord j))
        (canonicalEnd (R.terminalWord j)) := by
    simpa [terminalWord] using hrun0
  have hneg : predecessorShadow (R.terminalWord j) < 0 :=
    Runs.predecessorShadow_neg_of_canonical_run hrun
  have hpos : 0 < predecessorShadow (R.terminalWord j) := by
    simpa [terminalPredecessorShadow] using S.positiveShadow
  omega

/-- q>=5の局所三分岐からpositive-shadow枝を除いた局所二分岐。 -/
theorem terminal_dichotomy_at
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (hq : 5 ≤ R.windowLength j) :
    Nonempty (DeepLowerReplayTerminalAt R j) ∨
      R.TerminalSpecialC3At j := by
  rcases R.terminal_trichotomy_at j hq with hDeep | hPositive | hSpecial
  · exact Or.inl hDeep
  · exact False.elim
      (R.shortPositiveShadowTerminalAt_impossible
        j (Classical.choice hPositive))
  · exact Or.inr hSpecial

end FirstCriticalTransitionTowerData

/-- short positive-shadow terminal towerは存在しない。 -/
theorem shortPositiveShadowTerminalTower_impossible
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : ShortPositiveShadowTerminalTowerData hGap O) :
    False :=
  T.source.shortPositiveShadowTerminalAt_impossible
    (T.select 0) (T.shortPositive 0)

/-- first-critical towerの最終二分岐。 -/
theorem firstCriticalTerminal_dichotomy
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (DeepLowerReplayTerminalTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases firstCriticalTerminal_classification R with
    hDeep | hPositive | hSpecial
  · exact Or.inl hDeep
  · exact False.elim
      (shortPositiveShadowTerminalTower_impossible
        (Classical.choice hPositive))
  · exact Or.inr hSpecial

/-- short positive-shadowを除いたfirst-critical terminal outcome。 -/
inductive FirstCriticalReducedTerminalOutcomeTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Type
  | deepLowerReplay
      (data : DeepLowerReplayTerminalTowerData hGap O)
  | terminalSpecialC3
      (data : TerminalSpecialC3TransitionTowerData hGap O)

/-- reduced terminal outcomeを一つ選べる。 -/
theorem firstCriticalReducedTerminal_outcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (FirstCriticalReducedTerminalOutcomeTowerData hGap O) := by
  rcases firstCriticalTerminal_dichotomy R with hDeep | hSpecial
  · exact ⟨.deepLowerReplay (Classical.choice hDeep)⟩
  · exact ⟨.terminalSpecialC3 (Classical.choice hSpecial)⟩

end CollatzSecondLayer3
