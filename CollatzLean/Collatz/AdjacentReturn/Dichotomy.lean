import CollatzLean.Collatz.AdjacentReturn.Basic
import CollatzLean.Collatz.OddOrbit.StandardSelection
import CollatzLean.Collatz.Selection.Cofinal

/-!
# 隣接returnの最終二分岐
-/

namespace Collatz
namespace AdjacentReturn

open Selection

/-- 一つの非有界軌道はexpanding towerまたはcontracting towerを持つ。 -/
theorem dichotomy_on
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (ExpandingTower O) ∨ Nonempty (ContractingTower O) := by
  classical
  let S : O.FutureMinima := OddOrbit.Selection.futureMinima O hU
  have hS : S.IsStandard := by
    dsimp [S]
    exact OddOrbit.Selection.futureMinima_isStandard O hU
  let E : ℕ → Prop := fun j => (State.mk hU S hS j).IsExpanding
  by_cases hE : Cofinal E
  · left
    let s : ℕ → ℕ := Cofinal.select E hE
    refine ⟨{
      unbounded := hU
      minima := S
      standard := hS
      select := s
      select_strict := ?_
      expanding := ?_
    }⟩
    · exact Cofinal.select_strict E hE
    · intro n
      exact Cofinal.select_spec E hE n
  · obtain ⟨N, hN⟩ := Cofinal.eventually_not_of_not E hE
    let C : ℕ → Prop := fun j => (State.mk hU S hS j).IsContracting
    have hC : Cofinal C := by
      intro M
      let j := max M N
      have hjM : M ≤ j := le_max_left _ _
      have hjN : N ≤ j := le_max_right _ _
      have hnotE : ¬ E j := hN j hjN
      let R : State O := ⟨hU, S, hS, j⟩
      rcases R.expanding_or_contracting with hExp | hCon
      · exact False.elim (hnotE hExp)
      · exact ⟨j, hjM, hCon⟩
    right
    let s : ℕ → ℕ := Cofinal.select C hC
    refine ⟨{
      unbounded := hU
      minima := S
      standard := hS
      select := s
      select_strict := ?_
      contracting := ?_
    }⟩
    · exact Cofinal.select_strict C hC
    · intro n
      exact Cofinal.select_spec C hC n

/-- expanding adjacent towerが存在する。 -/
def HasExpandingTower : Prop := ∃ O : OddOrbit, Nonempty (ExpandingTower O)

/-- contracting adjacent towerが存在する。 -/
def HasContractingTower : Prop := ∃ O : OddOrbit, Nonempty (ContractingTower O)

/-- 非有界軌道の存在は二枝のどちらかへ無条件に落ちる。 -/
theorem dichotomy :
    HasUnboundedOddOrbit → HasExpandingTower ∨ HasContractingTower := by
  rintro ⟨O, hU⟩
  rcases dichotomy_on O hU with hE | hC
  · exact Or.inl ⟨O, hE⟩
  · exact Or.inr ⟨O, hC⟩

end AdjacentReturn
end Collatz
