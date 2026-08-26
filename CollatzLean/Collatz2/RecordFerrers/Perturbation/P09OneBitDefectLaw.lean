import CollatzLean.Collatz2.RecordFerrers.Perturbation.P08AdjacentTransferCarrySupport

/-!
# Record–Ferrers 摂動理論 9: 一ビット欠陥則と左右位置の決定

元の隣接二 block がともに内部 carry 1 であるとする。
全長を保存する隣接長さ移送の後でも外側 carry は 1 のままなので、
carry cocycle により、変形後の二つの境界 carry の和は
変形後の局所 carry `criticalCarry r' s'` に 1 を足したものに正確に一致する。

したがって、変形後の局所 carry が 1 なら欠陥は生じず、
0 なら左右どちらか一方だけに carry 0 が生じる。
さらに、欠陥が生じた場合に左か右かは、開始位置 `a` から最初の新 block `r'`
への carry だけで決まる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 隣接二境界の carry 総和。 -/
def pairCarrySum (a r s : ℕ) : ℕ :=
  criticalCarry a r + criticalCarry (a + r) s

/-- 左側の新境界だけで carry 0 が生じた状態。 -/
def LeftCarryDefect (a r s : ℕ) : Prop :=
  criticalCarry a r = 0 ∧
    criticalCarry (a + r) s = 1

/-- 右側の新境界だけで carry 0 が生じた状態。 -/
def RightCarryDefect (a r s : ℕ) : Prop :=
  criticalCarry a r = 1 ∧
    criticalCarry (a + r) s = 0

/--
全長保存移送後の二境界 carry の和は、
新しい二 block 自身の局所 carry に 1 を足したものに正確に一致する。

これは一ビット欠陥則の基本恒等式である。
-/
theorem adjacentTransfer_pairCarrySum_eq_localCarry_add_one
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    pairCarrySum a r' s' = criticalCarry r' s' + 1 := by
  have hMerged :=
    mergeCompatible_of_two_interior_carries a r s hOld.1 hOld.2
  have hOuterOld : criticalCarry a (r + s) = 1 := hMerged.2
  have hOuterNew : criticalCarry a (r' + s') = 1 := by
    rw [← T.total_eq]
    exact hOuterOld
  have hCocycle := criticalCarry_cocycle a r' s'
  unfold pairCarrySum
  rw [hOuterNew] at hCocycle
  omega

/--
元が内部/内部であるとき、全長保存移送後の二境界 carry の和は 1 または 2。
0 まで落ちることはない。
-/
theorem adjacentTransfer_pairCarrySum_eq_one_or_two
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    pairCarrySum a r' s' = 1 ∨ pairCarrySum a r' s' = 2 := by
  have hMaster :=
    adjacentTransfer_pairCarrySum_eq_localCarry_add_one hOld T
  rcases criticalCarry_eq_zero_or_one r' s' with hZero | hOne
  · rw [hZero] at hMaster
    left
    omega
  · rw [hOne] at hMaster
    right
    omega

/--
移送後にも二つの境界がともに carry 1 であることは、
新しい二 block 自身の局所 carry が 1 であることと同値。
欠陥が生じるかどうかは開始位置 `a` に依存しない。
-/
theorem adjacentTransfer_interiorPairCarry_iff_localCarry_one
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    InteriorPairCarry a r' s' ↔ criticalCarry r' s' = 1 := by
  have hMaster :=
    adjacentTransfer_pairCarrySum_eq_localCarry_add_one hOld T
  have hLeftLe : criticalCarry a r' ≤ 1 :=
    criticalCarry_le_one a r'
  have hRightLe : criticalCarry (a + r') s' ≤ 1 :=
    criticalCarry_le_one (a + r') s'
  constructor
  · intro hPair
    unfold InteriorPairCarry at hPair
    unfold pairCarrySum at hMaster
    rw [hPair.1, hPair.2] at hMaster
    omega
  · intro hLocal
    unfold pairCarrySum at hMaster
    rw [hLocal] at hMaster
    unfold InteriorPairCarry
    constructor <;> omega

/--
新しい二 block 自身の局所 carry が 0 であることは、
左右どちらか一方だけに carry 欠陥が生じることと同値。
二つ同時に 0 になることはない。
-/
theorem adjacentTransfer_localCarry_zero_iff_left_or_right_defect
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    criticalCarry r' s' = 0 ↔
      LeftCarryDefect a r' s' ∨ RightCarryDefect a r' s' := by
  have hMaster :=
    adjacentTransfer_pairCarrySum_eq_localCarry_add_one hOld T
  constructor
  · intro hLocal
    unfold pairCarrySum at hMaster
    rw [hLocal] at hMaster
    rcases criticalCarry_eq_zero_or_one a r' with hLeftZero | hLeftOne
    · left
      unfold LeftCarryDefect
      refine ⟨hLeftZero, ?_⟩
      rw [hLeftZero] at hMaster
      omega
    · right
      unfold RightCarryDefect
      refine ⟨hLeftOne, ?_⟩
      rw [hLeftOne] at hMaster
      omega
  · intro hDefect
    unfold pairCarrySum at hMaster
    rcases hDefect with hLeft | hRight
    · unfold LeftCarryDefect at hLeft
      rw [hLeft.1, hLeft.2] at hMaster
      omega
    · unfold RightCarryDefect at hRight
      rw [hRight.1, hRight.2] at hMaster
      omega

/--
局所 carry が 0 と分かっているとき、左欠陥であることは
開始位置から最初の新 block への carry が 0 であることだけで判定できる。
-/
theorem adjacentTransfer_leftCarryDefect_iff_leftCarry_zero
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0) :
    LeftCarryDefect a r' s' ↔ criticalCarry a r' = 0 := by
  have hMaster :=
    adjacentTransfer_pairCarrySum_eq_localCarry_add_one hOld T
  constructor
  · intro hLeft
    exact hLeft.1
  · intro hLeftZero
    unfold pairCarrySum at hMaster
    rw [hLocal, hLeftZero] at hMaster
    unfold LeftCarryDefect
    refine ⟨hLeftZero, ?_⟩
    omega

/--
局所 carry が 0 と分かっているとき、右欠陥であることは
開始位置から最初の新 block への carry が 1 であることだけで判定できる。
-/
theorem adjacentTransfer_rightCarryDefect_iff_leftCarry_one
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0) :
    RightCarryDefect a r' s' ↔ criticalCarry a r' = 1 := by
  have hMaster :=
    adjacentTransfer_pairCarrySum_eq_localCarry_add_one hOld T
  constructor
  · intro hRight
    exact hRight.1
  · intro hLeftOne
    unfold pairCarrySum at hMaster
    rw [hLocal, hLeftOne] at hMaster
    unfold RightCarryDefect
    refine ⟨hLeftOne, ?_⟩
    omega

/-- 左欠陥と右欠陥は同時には起こらない。 -/
theorem leftCarryDefect_rightCarryDefect_disjoint
    (a r s : ℕ) :
    ¬ (LeftCarryDefect a r s ∧ RightCarryDefect a r s) := by
  intro h
  unfold LeftCarryDefect at h
  unfold RightCarryDefect at h
  omega

/-- 移送後に欠陥が生じるなら、二境界 carry の和は正確に 1。 -/
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
