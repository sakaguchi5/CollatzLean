import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualPureBEffectiveWindingBridge

/-!
# Quantitative Boundary A -> PureB residual budget

前段で

  q_B - q_A <= (G - 1) * R(h)

まで carry history を消した。

ここでは Boundary A が定量的に

  q_A <= -K

だけ安全側へ離れており、B 側が

  0 <= q_B

なら、必ず

  K <= (G - 1) * R(h)

を満たさなければならないことを切り出す。

このファイルは新しい number theory を入れず、
A-side clearance と PureB residual budget を接続する最終算術 wrapper である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
純整数版の quantitative Boundary A lemma。

  q_A <= -K,
  0 <= q_B,
  q_B - q_A <= (G-1)R

なら

  K <= (G-1)R.
-/
theorem quantitativeBoundaryA_of_endpointDifferenceBound
    {qA qB G R K : ℤ}
    (hA : qA <= -K)
    (hB : 0 <= qB)
    (hDiff : qB - qA <= (G - 1) * R) :
    K <= (G - 1) * R := by
  linarith

namespace MinimalActualABObstructionPacket

/--
minimal bad `B` に対する quantitative Boundary A の必要条件。

Boundary A に clearance `K` があれば、PureB profile の bounded residual cost は
少なくとも

  K <= (G - 1) * R(h)

を支えなければならない。

この結論には intermediate carry の位置・順序・representative history は残らない。
-/
theorem quantitativeBoundaryA_le_gap_sub_one_mul_pureResidualCost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {K : ℤ}
    (hBoundary :
      normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) <= -K) :
    K <=
      ((wordTerminalGap
          (criticalBoundaryWord M.word.length) : ℤ) - 1) *
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  have hB : 0 <= (M.actual.q : ℤ) := by
    positivity
  have hDiff :=
    M.actualQ_sub_boundary_le_gap_sub_one_mul_pureResidualCost hL
  exact
    quantitativeBoundaryA_of_endpointDifferenceBound
      hBoundary hB hDiff

/--
clearance を natural number で与える場合の使いやすい wrapper。
-/
theorem quantitativeBoundaryA_nat_le_gap_sub_one_mul_pureResidualCost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {K : ℕ}
    (hBoundary :
      normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) <= -(K : ℤ)) :
    (K : ℤ) <=
      ((wordTerminalGap
          (criticalBoundaryWord M.word.length) : ℤ) - 1) *
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  exact
    M.quantitativeBoundaryA_le_gap_sub_one_mul_pureResidualCost
      hL hBoundary

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
