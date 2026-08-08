import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentState

/-!
# Adjacent Contracting Return

隣接 future-minimum word が

`3^r < 2^H`

を満たす局所整数枝。

actual affine 方程式と `next = start + Δ` から

`B = (2^H - 3^r) * start + 2^H * Δ`

を得る。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- `j` 番目の隣接 future-minimum return が contracting。 -/
def AdjacentContractingReturnAt
    (O : OddOrbit) (j : ℕ) : Prop :=
  Contracting (adjacentFutureMinimumWord O j)

/-- 一つの contracting 隣接 return。 -/
structure AdjacentContractingReturnData (O : OddOrbit) where
  state : AdjacentFutureMinimumReturnData O
  contracting : AdjacentContractingReturnAt O state.index

namespace AdjacentContractingReturnData

/-- contracting の純乗法不等式を state の `H,r` で読む。 -/
theorem contracting_inequality
    {O : OddOrbit} (D : AdjacentContractingReturnData O) :
    3 ^ D.state.length < 2 ^ D.state.totalExponent := by
  have hConWord : Contracting D.state.word := by
    simpa [AdjacentContractingReturnAt,
      AdjacentFutureMinimumReturnData.word] using D.contracting
  unfold Contracting at hConWord
  rw [D.state.oddSteps_word] at hConWord
  simpa [AdjacentFutureMinimumReturnData.totalExponent] using hConWord

/-- contracting determinant gap `2^H - 3^r`。 -/
noncomputable def multiplicativeGap
    {O : OddOrbit} (D : AdjacentContractingReturnData O) : ℕ :=
  2 ^ D.state.totalExponent - 3 ^ D.state.length

/-- contracting gap は正。 -/
theorem multiplicativeGap_pos
    {O : OddOrbit} (D : AdjacentContractingReturnData O) :
    0 < D.multiplicativeGap := by
  unfold multiplicativeGap
  exact Nat.sub_pos_of_lt D.contracting_inequality

/--
Adjacent Contracting Return の exact 局所整数方程式。
-/
theorem return_identity
    {O : OddOrbit} (D : AdjacentContractingReturnData O) :
    D.state.affineConstant =
      D.multiplicativeGap * D.state.startValue +
        2 ^ D.state.totalExponent * D.state.valueGap := by
  have hEq := D.state.scaled_return_equation
  have hValue := D.state.nextValue_eq_startValue_add_valueGap
  have hCon := D.contracting_inequality
  have hGap :
      3 ^ D.state.length + D.multiplicativeGap =
        2 ^ D.state.totalExponent := by
    unfold multiplicativeGap
    omega
  rw [hValue] at hEq
  nlinarith [hGap]

end AdjacentContractingReturnData

/-- contracting 隣接 return が cofinal に現れる tower。 -/
structure AdjacentContractingReturnTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  select : ℕ → ℕ
  select_strict : StrictMono select
  contracting : ∀ n : ℕ, AdjacentContractingReturnAt O (select n)

namespace AdjacentContractingReturnTowerData

/-- 選択添字は自身以上なので tower は標準 future-minimum 列で cofinal。 -/
theorem select_ge
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) :
    n ≤ T.select n :=
  nat_le_strictMono_apply T.select T.select_strict n

/-- tower の第n項を局所 contracting data として読む。 -/
def state
    {O : OddOrbit}
    (T : AdjacentContractingReturnTowerData O)
    (n : ℕ) : AdjacentContractingReturnData O :=
  { state := AdjacentFutureMinimumReturnData.ofIndex O T.unbounded (T.select n)
    contracting := T.contracting n }

end AdjacentContractingReturnTowerData

/-- 非有界軌道上の Adjacent Contracting Return obstruction。 -/
def HasAdjacentContractingReturnTower : Prop :=
  ∃ O : OddOrbit, Nonempty (AdjacentContractingReturnTowerData O)

/-- 最終局所整数枝2の排除原理。 -/
def AdjacentContractingReturnExclusionPrinciple : Prop :=
  ¬ HasAdjacentContractingReturnTower

end CollatzSecondLayer3
