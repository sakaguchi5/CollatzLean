import CollatzLean.CollatzSecondLayer2.FinalPositiveReduction
import CollatzLean.CollatzSecondLayer2.UnifiedSpecialC3Obstruction

/-!
# 最終正還元：first-critical枝をterminal枝へ展開

互換APIとして、first-critical枝を

* deep lower-replay terminal
* short positive-shadow terminal
* terminal Special C3

へ展開する従来の五分岐を残す。

さらにsigned replayの符号保存によりshort positive-shadow枝を排除し、
terminal Special C3をSpecial C3中央枝のcritical-terminal形へ吸収する。

最終対象は

* anchored one-sided meander
* unified Special C3 obstruction
  * polynomial
  * discounted
  * critical-terminal
* deep lower-replay terminal

の三枝となる。
-/

namespace CollatzSecondLayer2

/-- 一つの非有界軌道に対するterminal展開済み最終五分岐。 -/
theorem unboundedOrbit_final_terminal_pentachotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (DeepLowerReplayTerminalTowerData hGap O) ∨
      Nonempty (ShortPositiveShadowTerminalTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases unboundedOrbit_final_positive_trichotomy_on
      hGap O hU with hM | hSpecial | hCritical
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hCritical with ⟨R⟩
    rcases firstCriticalTerminal_classification R with
      hDeep | hPositive | hTerminal
    · exact Or.inr (Or.inr (Or.inl hDeep))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hPositive)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTerminal)))

/-- 非有界軌道上のdeep lower-replay terminal tower。 -/
def HasDeepLowerReplayTerminalTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (DeepLowerReplayTerminalTowerData hGap O)

/-- 非有界軌道上のshort positive-shadow terminal tower。 -/
def HasShortPositiveShadowTerminalTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (ShortPositiveShadowTerminalTowerData hGap O)

/-- terminal三枝まで展開した非有界odd-only軌道の最終五分岐。 -/
theorem unbounded_odd_orbit_final_terminal_pentachotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasDeepLowerReplayTerminalTower hGap ∨
      HasShortPositiveShadowTerminalTower hGap ∨
      HasTerminalSpecialC3TransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_terminal_pentachotomy_on
      hGap O hU with hM | hSpecial | hDeep | hPositive | hTerminal
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨O, hU, hDeep⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨O, hU, hPositive⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨O, hU, hTerminal⟩)))

/-- terminal展開後の全対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_final_terminal_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasSpecialC3ObstructionTower)
    (hDeep : ¬ HasDeepLowerReplayTerminalTower hGap)
    (hPositive : ¬ HasShortPositiveShadowTerminalTower hGap)
    (hTerminal : ¬ HasTerminalSpecialC3TransitionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_final_terminal_pentachotomy
      hGap hU with hM | hS | hD | hP | hT
  · exact hMeander hM
  · exact hSpecial hS
  · exact hDeep hD
  · exact hPositive hP
  · exact hTerminal hT

/-- short positive-shadow terminal towerは無条件に存在しない。 -/
theorem no_HasShortPositiveShadowTerminalTower
    (hGap : TwoThreeGapPolynomialBound) :
    ¬ HasShortPositiveShadowTerminalTower hGap := by
  rintro ⟨O, hU, ⟨T⟩⟩
  exact shortPositiveShadowTerminalTower_impossible T

/--
short positive-shadowを除いた、一つの非有界軌道に対する最終四分岐。
-/
theorem unboundedOrbit_final_terminal_quadrichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (SpecialC3ObstructionTowerData O) ∨
      Nonempty (DeepLowerReplayTerminalTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  rcases unboundedOrbit_final_positive_trichotomy_on
      hGap O hU with hM | hSpecial | hCritical
  · exact Or.inl hM
  · exact Or.inr (Or.inl hSpecial)
  · rcases hCritical with ⟨R⟩
    rcases firstCriticalTerminal_dichotomy R with hDeep | hTerminal
    · exact Or.inr (Or.inr (Or.inl hDeep))
    · exact Or.inr (Or.inr (Or.inr hTerminal))

/-- short positive-shadowを除いた非有界odd-only軌道の最終四分岐。 -/
theorem unbounded_odd_orbit_final_terminal_quadrichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasSpecialC3ObstructionTower ∨
      HasDeepLowerReplayTerminalTower hGap ∨
      HasTerminalSpecialC3TransitionTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_terminal_quadrichotomy_on
      hGap O hU with hM | hSpecial | hDeep | hTerminal
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨O, hU, hDeep⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨O, hU, hTerminal⟩))

/-- reduced terminal四対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_reduced_terminal_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasSpecialC3ObstructionTower)
    (hDeep : ¬ HasDeepLowerReplayTerminalTower hGap)
    (hTerminal : ¬ HasTerminalSpecialC3TransitionTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_final_terminal_quadrichotomy
      hGap hU with hM | hS | hD | hT
  · exact hMeander hM
  · exact hSpecial hS
  · exact hDeep hD
  · exact hTerminal hT


/-- 非有界軌道上の統合済みSpecial C3 obstruction。 -/
def HasFinalSpecialC3ObstructionTower : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      Nonempty (UnifiedSpecialC3ObstructionTowerData O)

/--
terminal Special C3を統合中央枝へ吸収した、一つの非有界軌道の最終三分岐。
-/
theorem unboundedOrbit_final_terminal_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (UnifiedSpecialC3ObstructionTowerData O) ∨
      Nonempty (DeepLowerReplayTerminalTowerData hGap O) := by
  rcases unboundedOrbit_final_terminal_quadrichotomy_on
      hGap O hU with hM | hSpecial | hDeep | hTerminal
  · exact Or.inl hM
  · rcases hSpecial with ⟨S⟩
    exact Or.inr (Or.inl ⟨S.toUnified⟩)
  · exact Or.inr (Or.inr hDeep)
  · rcases hTerminal with ⟨T⟩
    exact Or.inr (Or.inl ⟨T.toUnifiedObstruction⟩)

/-- terminal Special C3吸収後の非有界odd-only軌道の最終三分岐。 -/
theorem unbounded_odd_orbit_final_terminal_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasFinalSpecialC3ObstructionTower ∨
      HasDeepLowerReplayTerminalTower hGap := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_final_terminal_trichotomy_on
      hGap O hU with hM | hSpecial | hDeep
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hDeep⟩)

/-- 最終三対象を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit_of_final_three_exclusions
    (hGap : TwoThreeGapPolynomialBound)
    (hMeander : ¬ HasAnchoredOneSidedMeander)
    (hSpecial : ¬ HasFinalSpecialC3ObstructionTower)
    (hDeep : ¬ HasDeepLowerReplayTerminalTower hGap) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_final_terminal_trichotomy
      hGap hU with hM | hS | hD
  · exact hMeander hM
  · exact hSpecial hS
  · exact hDeep hD

end CollatzSecondLayer2
