import CollatzLean.Collatz.AdjacentReturn.Dichotomy
import CollatzLean.Collatz.AdjacentReturn.Valuation

/-!
# 最終的に全区間が収縮する tail

`dichotomy_on` の収縮側で実際には得られている
「十分後のすべての adjacent return が収縮する」という情報を
弱い cofinal selector へ落とさず、そのまま保持する。
-/

namespace Collatz
namespace AdjacentReturn

open Selection

/--
標準 future-minimum 列上で、ある cutoff 以後の全 adjacent return が
収縮するという強い tail データ。
-/
structure EventuallyContractingTailData (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinima
  standard : minima.IsStandard
  cutoff : ℕ
  contracting : ∀ j : ℕ, cutoff ≤ j →
    (State.mk unbounded minima standard j).IsContracting

namespace EventuallyContractingTailData

/-- cutoff から n 個進んだ連続 adjacent state。 -/
def state {O : OddOrbit} (D : EventuallyContractingTailData O) (n : ℕ) :
    State O :=
  ⟨D.unbounded, D.minima, D.standard, D.cutoff + n⟩

/-- tail の各 state は収縮する。 -/
theorem state_contracting
    {O : OddOrbit} (D : EventuallyContractingTailData O) (n : ℕ) :
    (D.state n).IsContracting := by
  exact D.contracting (D.cutoff + n) (by omega)

/-- 連続 tail を既存の `ContractingTower` API へ埋め込む。 -/
def toContractingTower
    {O : OddOrbit} (D : EventuallyContractingTailData O) :
    ContractingTower O where
  unbounded := D.unbounded
  minima := D.minima
  standard := D.standard
  select := fun n => D.cutoff + n
  select_strict := by
    intro a b hab
    exact Nat.add_lt_add_left hab D.cutoff
  contracting := by
    intro n
    exact D.state_contracting n

@[simp] theorem toContractingTower_tower_at
    {O : OddOrbit} (D : EventuallyContractingTailData O) (n : ℕ) :
    (D.toContractingTower.tower_at n) = D.state n := rfl

/-- 連続 tail では state n の next index が state (n+1) の start index と一致する。 -/
theorem nextIndex_eq_next_startIndex
    {O : OddOrbit} (D : EventuallyContractingTailData O) (n : ℕ) :
    (D.state n).nextIndex = (D.state (n + 1)).startIndex := by
  unfold State.nextIndex State.startIndex state
  congr 1

/-- 連続 tail では next value と次 state の start value が一致する。 -/
theorem nextValue_eq_next_startValue
    {O : OddOrbit} (D : EventuallyContractingTailData O) (n : ℕ) :
    (D.state n).nextValue = (D.state (n + 1)).startValue := by
  unfold State.nextValue State.startValue
  rw [D.nextIndex_eq_next_startIndex n]

/-- 連続 tail では next future-minimum depth と次 start depth が一致する。 -/
theorem valuation_nextDepth_eq_next_startDepth
    {O : OddOrbit} (D : EventuallyContractingTailData O)
    (n : ℕ)
    (V : State.ValuationData (D.state n))
    (W : State.ValuationData (D.state (n + 1))) :
    V.nextDepth = W.startDepth := by
  have hvalue :
      (D.state n).nextValue + 1 =
        (D.state (n + 1)).startValue + 1 := by
    rw [D.nextValue_eq_next_startValue n]
  have hW :
      TwoAdic.ExactFactor
        ((D.state n).nextValue + 1)
        W.startDepth W.startOddPart := by
    rw [hvalue]
    exact W.startFactor
  exact TwoAdic.exponent_unique V.nextFactor hW

end EventuallyContractingTailData

/-- 強化された収縮側 tail の存在命題。 -/
def HasEventuallyContractingTail : Prop :=
  ∃ O : OddOrbit, Nonempty (EventuallyContractingTailData O)

/--
非有界 odd orbit は expanding cofinal tower か、最終的に全区間が収縮する tail を持つ。
既存 `dichotomy_on` より収縮側の情報を強く保持する。
-/
theorem dichotomy_on_strong
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (ExpandingTower O) ∨
      Nonempty (EventuallyContractingTailData O) := by
  classical
  let S : O.FutureMinima := OddOrbit.Selection.futureMinima O hU
  have hS : S.IsStandard := by
    dsimp [S]
    exact OddOrbit.Selection.futureMinima_isStandard O hU
  let E : ℕ → Prop :=
    fun j => (State.mk hU S hS j).IsExpanding
  by_cases hE : Cofinal E
  · left
    let s : ℕ → ℕ := Cofinal.select E hE
    refine ⟨{
      unbounded := hU
      minima := S
      standard := hS
      select := s
      select_strict := Cofinal.select_strict E hE
      expanding := fun n => Cofinal.select_spec E hE n
    }⟩
  · right
    obtain ⟨N, hN⟩ := Cofinal.eventually_not_of_not E hE
    refine ⟨{
      unbounded := hU
      minima := S
      standard := hS
      cutoff := N
      contracting := ?_
    }⟩
    intro j hj
    have hnotE : ¬ E j := hN j hj
    let R : State O := ⟨hU, S, hS, j⟩
    rcases R.expanding_or_contracting with hExp | hCon
    · exact False.elim (hnotE hExp)
    · exact hCon

/-- 強化された大域二分岐。 -/
theorem dichotomy_strong :
    HasUnboundedOddOrbit →
      HasExpandingTower ∨ HasEventuallyContractingTail := by
  rintro ⟨O, hU⟩
  rcases dichotomy_on_strong O hU with hE | hC
  · exact Or.inl ⟨O, hE⟩
  · exact Or.inr ⟨O, hC⟩

end AdjacentReturn
end Collatz
