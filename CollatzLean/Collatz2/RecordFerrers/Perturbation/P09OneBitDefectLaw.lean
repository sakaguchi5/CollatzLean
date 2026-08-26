import CollatzLean.Collatz2.RecordFerrers.Perturbation.P08AdjacentTransferCarrySupport

/-!
# Record–Ferrers 摂動理論 9: one-bit defect law

元の隣接二 block がともに interior carry 1 であるとする。
total length を保存する任意の隣接 length transfer 後、二つの carry の和は 1 または 2。
したがって局所変形は一度に高々一個の carry defect しか生成できない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 隣接二境界の carry 総和。 -/
def pairCarrySum (a r s : ℕ) : ℕ :=
  criticalCarry a r + criticalCarry (a + r) s

/--
元が interior/interior のとき、total-preserving transfer 後の pair carry sum は 1 または 2。
0 まで落ちることはない。
-/
theorem adjacentTransfer_pairCarrySum_eq_one_or_two
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    pairCarrySum a r' s' = 1 ∨ pairCarrySum a r' s' = 2 := by
  have hMerged :=
    mergeCompatible_of_two_interior_carries a r s hOld.1 hOld.2
  have hOuterOld : criticalCarry a (r + s) = 1 := hMerged.2
  have hOuterNew : criticalCarry a (r' + s') = 1 := by
    rw [← T.total_eq]
    exact hOuterOld
  have hCocycle := criticalCarry_cocycle a r' s'
  have hLocal := criticalCarry_eq_zero_or_one r' s'
  unfold pairCarrySum
  rcases hLocal with hZero | hOne
  · rw [hZero, hOuterNew] at hCocycle
    left
    omega
  · rw [hOne, hOuterNew] at hCocycle
    right
    omega

/-- transfer 後に defect が生じるなら、pair carry sum は exact に 1。 -/
theorem adjacentTransfer_pairCarrySum_eq_one_of_not_two
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hNotTwo : pairCarrySum a r' s' ≠ 2) :
    pairCarrySum a r' s' = 1 := by
  rcases adjacentTransfer_pairCarrySum_eq_one_or_two hOld T with hOne | hTwo
  · exact hOne
  · exact False.elim (hNotTwo hTwo)

end RecordFerrers
end Collatz2
