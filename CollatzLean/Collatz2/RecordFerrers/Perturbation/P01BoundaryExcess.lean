import CollatzLean.Collatz2.RecordFerrers.Record.CarryStatistics

/-!
# Record–Ferrers 摂動理論 1: 境界 excess

record skeleton の先頭からいくつかの minimal block を積み上げたとき、
実際に必要な minimal depth と critical roof の高さとの差を整数で保持する。
既存の zero-carry 計数定理により、この量は carry 0 の累積個数そのものになる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/--
`start` から `rs` を minimal block として積んだときの signed boundary excess。
正なら critical roof よりその分だけ上にいる。
-/
def boundaryExcessInt (start : ℕ) (rs : List ℕ) : ℤ :=
  (criticalHeight start : ℤ) + (localMinimalDepthSum rs : ℤ) -
    (criticalHeight (start + rs.sum) : ℤ)

/-- 境界 excess は zero-carry の累積個数と exact に一致する。 -/
theorem boundaryExcessInt_eq_zeroCarryCountFrom
    (start : ℕ)
    (rs : List ℕ) :
    boundaryExcessInt start rs = (zeroCarryCountFrom start rs : ℤ) := by
  have hNat :=
    criticalHeight_add_localMinimalDepthSum_eq_add_zeroCarryCount
      start rs
  have hInt :
      (criticalHeight start : ℤ) + (localMinimalDepthSum rs : ℤ) =
        (criticalHeight (start + rs.sum) : ℤ) +
          (zeroCarryCountFrom start rs : ℤ) := by
    exact_mod_cast hNat
  unfold boundaryExcessInt
  linarith

/-- 境界 excess は常に非負。 -/
theorem boundaryExcessInt_nonneg
    (start : ℕ)
    (rs : List ℕ) :
    0 ≤ boundaryExcessInt start rs := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  positivity

@[simp] theorem boundaryExcessInt_nil
    (start : ℕ) :
    boundaryExcessInt start [] = 0 := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  rfl

end Skeleton

end RecordFerrers
end Collatz2
