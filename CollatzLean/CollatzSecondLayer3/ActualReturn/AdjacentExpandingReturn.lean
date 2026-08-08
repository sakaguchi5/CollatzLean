import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentState

/-!
# Adjacent Expanding Return

隣接 future-minimum word が

`2^H < 3^r`

を満たす局所整数枝。

actual affine 方程式と `next = start + Δ` から

`2^H * Δ = (3^r - 2^H) * start + B`

を得る。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- `j` 番目の隣接 future-minimum return が expanding。 -/
def AdjacentExpandingReturnAt
    (O : OddOrbit) (j : ℕ) : Prop :=
  Expanding (adjacentFutureMinimumWord O j)

/-- 一つの expanding 隣接 return。 -/
structure AdjacentExpandingReturnData (O : OddOrbit) where
  state : AdjacentFutureMinimumReturnData O
  expanding : AdjacentExpandingReturnAt O state.index

namespace AdjacentExpandingReturnData

/-- expanding の純乗法不等式を state の `H,r` で読む。 -/
theorem expanding_inequality
    {O : OddOrbit} (D : AdjacentExpandingReturnData O) :
    2 ^ D.state.totalExponent < 3 ^ D.state.length := by
  have hExpWord : Expanding D.state.word := by
    simpa [AdjacentExpandingReturnAt,
      AdjacentFutureMinimumReturnData.word] using D.expanding
  unfold Expanding at hExpWord
  rw [D.state.oddSteps_word] at hExpWord
  simpa [AdjacentFutureMinimumReturnData.totalExponent] using hExpWord

/-- expanding determinant gap `3^r - 2^H`。 -/
noncomputable def multiplicativeGap
    {O : OddOrbit} (D : AdjacentExpandingReturnData O) : ℕ :=
  3 ^ D.state.length - 2 ^ D.state.totalExponent

/-- expanding gap は正。 -/
theorem multiplicativeGap_pos
    {O : OddOrbit} (D : AdjacentExpandingReturnData O) :
    0 < D.multiplicativeGap := by
  unfold multiplicativeGap
  exact Nat.sub_pos_of_lt D.expanding_inequality

/--
Adjacent Expanding Return の exact 局所整数方程式。
-/
theorem return_identity
    {O : OddOrbit} (D : AdjacentExpandingReturnData O) :
    2 ^ D.state.totalExponent * D.state.valueGap =
      D.multiplicativeGap * D.state.startValue +
        D.state.affineConstant := by
  have hEq := D.state.scaled_return_equation
  have hValue := D.state.nextValue_eq_startValue_add_valueGap
  have hExp := D.expanding_inequality
  have hGap :
      2 ^ D.state.totalExponent + D.multiplicativeGap =
        3 ^ D.state.length := by
    unfold multiplicativeGap
    omega
  rw [hValue] at hEq
  nlinarith [hGap]

end AdjacentExpandingReturnData

/-- expanding 隣接 return が cofinal に現れる tower。 -/
structure AdjacentExpandingReturnTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  select : ℕ → ℕ
  select_strict : StrictMono select
  expanding : ∀ n : ℕ, AdjacentExpandingReturnAt O (select n)

namespace AdjacentExpandingReturnTowerData

/-- 選択添字は自身以上なので tower は標準 future-minimum 列で cofinal。 -/
theorem select_ge
    {O : OddOrbit}
    (T : AdjacentExpandingReturnTowerData O)
    (n : ℕ) :
    n ≤ T.select n :=
  nat_le_strictMono_apply T.select T.select_strict n

/-- tower の第n項を局所 expanding data として読む。 -/
def state
    {O : OddOrbit}
    (T : AdjacentExpandingReturnTowerData O)
    (n : ℕ) : AdjacentExpandingReturnData O :=
  { state := AdjacentFutureMinimumReturnData.ofIndex O T.unbounded (T.select n)
    expanding := T.expanding n }

end AdjacentExpandingReturnTowerData

/-- 非有界軌道上の Adjacent Expanding Return obstruction。 -/
def HasAdjacentExpandingReturnTower : Prop :=
  ∃ O : OddOrbit, Nonempty (AdjacentExpandingReturnTowerData O)

/-- 最終局所整数枝1の排除原理。 -/
def AdjacentExpandingReturnExclusionPrinciple : Prop :=
  ¬ HasAdjacentExpandingReturnTower

end CollatzSecondLayer3
