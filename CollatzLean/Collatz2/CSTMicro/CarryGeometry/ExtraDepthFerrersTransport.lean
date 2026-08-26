import CollatzLean.Collatz2.CSTMicro.CarryGeometry.UniversalRankTopFerrersStep

/-!
# Extra-depth transport across Ferrers steps

first-passage Ferrers move `01 -> 10` は odd-only rank geometry で
selected cut の prefix two-depth を exact に 1 減らす。
critical roof は endpoints `(H,m,k)` のみで決まるので、word-specific depth

  extraDepth(k) = criticalHeight(k) - prefixTwoDepth(k)

は selected cut だけ exact に 1 増え、他 cut では不変となる。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersStep

/-- selected cut では upper extra-depth が exact に一層増える。 -/
theorem extraDepth_rankUpper_eq_rankLower_add_one_at_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    Collatz2.Word.extraDepth
        S.edge.rankUpperExponentWord S.edge.rankCut =
      Collatz2.Word.extraDepth
          S.edge.rankLowerExponentWord S.edge.rankCut + 1 := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hSlack := S.rankCell_oneStepFirstPassageSlack hLowerFP
  have hCrit :
      S.edge.position + 1 ≤ Collatz2.Word.criticalHeight S.edge.rankCut :=
    Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hSlack
  unfold Collatz2.Word.extraDepth
  rw [S.edge.prefixTwoDepth_rankCut_eq_position hEdgeUpperFP]
  rw [S.edge.prefixTwoDepth_rankCut_eq_position_add_one hEdgeLowerFP]
  omega

/-- selected cut 以外では extra-depth は exact に不変。 -/
theorem extraDepth_rankUpper_eq_rankLower_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    Collatz2.Word.extraDepth S.edge.rankUpperExponentWord k =
      Collatz2.Word.extraDepth S.edge.rankLowerExponentWord k := by
  have hDepth :=
    S.prefixTwoDepth_rankUpper_eq_rankLower_of_ne_rankCut hLowerFP hk
  unfold Collatz2.Word.extraDepth
  rw [hDepth]

end FerrersStep

/-- parity endpoint 自身から読む odd-only extra-depth profile。 -/
def parityExtraDepth
    (v : ParityWord)
    (k : ℕ) : ℕ :=
  Collatz2.Word.extraDepth (exponentWordOfParity v) k

namespace FerrersStep

/-- endpoint representation でも selected column は exact に +1。 -/
theorem parityExtraDepth_selected_step
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    parityExtraDepth upper S.edge.rankCut =
      parityExtraDepth lower S.edge.rankCut + 1 := by
  have hCore :=
    S.extraDepth_rankUpper_eq_rankLower_add_one_at_rankCut hLowerFP
  have hUpperWord :
      exponentWordOfParity upper = S.edge.rankUpperExponentWord := by
    unfold AdjacentFerrersSwap.rankUpperExponentWord
    exact congrArg exponentWordOfParity S.upper_eq
  have hLowerWord :
      exponentWordOfParity lower = S.edge.rankLowerExponentWord := by
    unfold AdjacentFerrersSwap.rankLowerExponentWord
    exact congrArg exponentWordOfParity S.lower_eq
  unfold parityExtraDepth
  rw [hUpperWord, hLowerWord]
  exact hCore

/-- endpoint representation でも non-selected column は不変。 -/
theorem parityExtraDepth_step_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    parityExtraDepth upper k = parityExtraDepth lower k := by
  have hCore :=
    S.extraDepth_rankUpper_eq_rankLower_of_ne_rankCut hLowerFP hk
  have hUpperWord :
      exponentWordOfParity upper = S.edge.rankUpperExponentWord := by
    unfold AdjacentFerrersSwap.rankUpperExponentWord
    exact congrArg exponentWordOfParity S.upper_eq
  have hLowerWord :
      exponentWordOfParity lower = S.edge.rankLowerExponentWord := by
    unfold AdjacentFerrersSwap.rankLowerExponentWord
    exact congrArg exponentWordOfParity S.lower_eq
  unfold parityExtraDepth
  rw [hUpperWord, hLowerWord]
  exact hCore

/-- one-step profile law in indicator form。 -/
theorem parityExtraDepth_step
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (k : ℕ) :
    parityExtraDepth upper k =
      parityExtraDepth lower k + if k = S.edge.rankCut then 1 else 0 := by
  by_cases hk : k = S.edge.rankCut
  · subst k
    rw [ite_eq_left rfl]
    exact S.parityExtraDepth_selected_step hLowerFP
  · rw [ite_eq_right hk]
    simp only [Nat.add_zero]
    exact S.parityExtraDepth_step_of_ne_rankCut hLowerFP hk

end FerrersStep

end CSTMicro
end Collatz2
