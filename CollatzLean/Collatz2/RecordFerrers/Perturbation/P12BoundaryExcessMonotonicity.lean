import CollatzLean.Collatz2.RecordFerrers.Perturbation.P11OldBoundaryDestruction

/-!
# Record–Ferrers 摂動理論 12: boundary excess の一般単調性

これまでの `excess = zero-carry 個数` を append に沿う exact 更新式へ持ち上げる。
後続 block を何個追加しても boundary excess は減少しない。
したがって一度正の defect が生じると、旧 block 境界だけをたどって defect を消すことはできない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/--
block 列を後ろへ追加したときの boundary excess の exact 分解。
増分は追加 tail 内に現れる zero-carry の個数そのもの。
-/
theorem boundaryExcessInt_append
    (start : ℕ)
    (leftCtx tail : List ℕ) :
    boundaryExcessInt start (leftCtx ++ tail) =
      boundaryExcessInt start leftCtx +
        (zeroCarryCountFrom (start + leftCtx.sum) tail : ℤ) := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom,
      boundaryExcessInt_eq_zeroCarryCountFrom]
  have h := zeroCarryCountFrom_append start leftCtx tail
  exact_mod_cast h

/-- boundary excess は任意 tail の追加に対して単調非減少。 -/
theorem boundaryExcessInt_le_append
    (start : ℕ)
    (leftCtx tail : List ℕ) :
    boundaryExcessInt start leftCtx ≤
      boundaryExcessInt start (leftCtx ++ tail) := by
  rw [boundaryExcessInt_append]
  have hNonneg :
      0 ≤ (zeroCarryCountFrom (start + leftCtx.sum) tail : ℤ) := by
    positivity
  linarith

/--
tail 内に zero-carry が少なくとも一つあれば boundary excess は strict に増える。
逆に strict 増加したなら tail 内に zero-carry が存在する。
-/
theorem boundaryExcessInt_lt_append_iff
    (start : ℕ)
    (leftCtx tail : List ℕ) :
    boundaryExcessInt start leftCtx <
        boundaryExcessInt start (leftCtx ++ tail) ↔
      0 < zeroCarryCountFrom (start + leftCtx.sum) tail := by
  rw [boundaryExcessInt_append]
  constructor
  · intro h
    have hZ :
        0 < (zeroCarryCountFrom (start + leftCtx.sum) tail : ℤ) := by
      linarith
    exact_mod_cast hZ
  · intro h
    have hZ :
        0 < (zeroCarryCountFrom (start + leftCtx.sum) tail : ℤ) := by
      exact_mod_cast h
    linarith

/-- 一度正になった boundary excess は任意 tail を追加しても正のまま。 -/
theorem boundaryExcessInt_pos_append_of_pos
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hPos : 0 < boundaryExcessInt start leftCtx) :
    0 < boundaryExcessInt start (leftCtx ++ tail) := by
  exact lt_of_lt_of_le hPos
    (boundaryExcessInt_le_append start leftCtx tail)

/--
excess が 0 のまま tail を通過できることと、tail に zero-carry が一つもないことは同値。
-/
theorem boundaryExcessInt_append_eq_iff_zeroCarryCount_eq_zero
    (start : ℕ)
    (leftCtx tail : List ℕ) :
    boundaryExcessInt start (leftCtx ++ tail) =
        boundaryExcessInt start leftCtx ↔
      zeroCarryCountFrom (start + leftCtx.sum) tail = 0 := by
  rw [boundaryExcessInt_append]
  constructor
  · intro h
    have hZ :
        (zeroCarryCountFrom (start + leftCtx.sum) tail : ℤ) = 0 := by
      linarith
    exact_mod_cast hZ
  · intro h
    rw [h]
    norm_num

end Skeleton

end RecordFerrers
end Collatz2
