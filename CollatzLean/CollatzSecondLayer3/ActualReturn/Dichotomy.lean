import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentExpandingReturn
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentContractingReturn
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# 発散反例の隣接 future-minimum 最終二分岐

first crossing の存在を一切仮定しない。
各標準 future-minimum の隣接区間は valid nonempty exponent word なので、必ず

* `2^H < 3^r` : Adjacent Expanding Return
* `3^r < 2^H` : Adjacent Contracting Return

のどちらかに入る。

二色のうち expanding が cofinal なら expanding tower を選び、そうでなければ
十分後は expanding でないため contracting が cofinal となる。
従って非有界軌道は無条件に二つの局所整数 tower のどちらかを生成する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 各隣接 future-minimum return は expanding または contracting。 -/
theorem adjacentReturn_expanding_or_contracting
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) :
    AdjacentExpandingReturnAt O j ∨
      AdjacentContractingReturnAt O j := by
  let R := AdjacentFutureMinimumReturnData.ofIndex O hU j
  change Expanding R.word ∨ Contracting R.word
  exact R.expanding_or_contracting

/--
一つの非有界軌道は、Adjacent Expanding Return tower または
Adjacent Contracting Return tower のどちらかを無条件に持つ。
-/
theorem unboundedOrbit_adjacentReturn_dichotomy_on
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Nonempty (AdjacentExpandingReturnTowerData O) ∨
      Nonempty (AdjacentContractingReturnTowerData O) := by
  classical
  let E : ℕ → Prop := fun j => AdjacentExpandingReturnAt O j
  by_cases hE : Cofinally E
  · left
    let s : ℕ → ℕ := Cofinally.select E hE
    refine ⟨{
      unbounded := hU
      select := s
      select_strict := ?_
      expanding := ?_
    }⟩
    · exact Cofinally.select_strict E hE
    · intro n
      exact Cofinally.select_spec E hE n
  · obtain ⟨N, hN⟩ := Cofinally.eventually_not_of_not E hE
    let C : ℕ → Prop := fun j => AdjacentContractingReturnAt O j
    have hC : Cofinally C := by
      intro M
      let j := max M N
      have hjM : M ≤ j := by
        dsimp [j]
        exact le_max_left _ _
      have hjN : N ≤ j := by
        dsimp [j]
        exact le_max_right _ _
      have hnotE : ¬ E j := hN j hjN
      rcases adjacentReturn_expanding_or_contracting O hU j with hExp | hCon
      · exact False.elim (hnotE hExp)
      · exact ⟨j, hjM, hCon⟩
    right
    let s : ℕ → ℕ := Cofinally.select C hC
    refine ⟨{
      unbounded := hU
      select := s
      select_strict := ?_
      contracting := ?_
    }⟩
    · exact Cofinally.select_strict C hC
    · intro n
      exact Cofinally.select_spec C hC n

/-- 非有界 odd-only 軌道の存在を二つの隣接-return局所整数枝へ無条件に還元する。 -/
theorem unbounded_odd_orbit_adjacentReturn_dichotomy :
    HasUnboundedOddOrbit →
      HasAdjacentExpandingReturnTower ∨
        HasAdjacentContractingReturnTower := by
  rintro ⟨O, hU⟩
  rcases unboundedOrbit_adjacentReturn_dichotomy_on O hU with hExp | hCon
  · exact Or.inl ⟨O, hExp⟩
  · exact Or.inr ⟨O, hCon⟩

/--
互換用名称。新しい actual-return dichotomy は仮定ではなく Lean 内で成立する。
-/
def ActualReturnDichotomyPrinciple : Prop :=
  HasUnboundedOddOrbit →
    HasAdjacentExpandingReturnTower ∨
      HasAdjacentContractingReturnTower

/-- 新しい actual-return dichotomy principle は無条件に証明済み。 -/
theorem actualReturnDichotomyPrinciple :
    ActualReturnDichotomyPrinciple :=
  unbounded_odd_orbit_adjacentReturn_dichotomy

end CollatzSecondLayer3
