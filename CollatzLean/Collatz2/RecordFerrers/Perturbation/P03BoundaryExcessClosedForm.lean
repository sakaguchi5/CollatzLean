import CollatzLean.Collatz2.RecordFerrers.Perturbation.P02BoundaryExcessRecurrence

/-!
# Record–Ferrers 摂動理論 3: excess の閉形式

各 block 境界で `1 - carry` を足した総量が boundary excess である。
既存の `carrySumFrom` を使うと、これは「block 数 - carry 1 の個数」として exact に書ける。
-/

namespace Collatz2
namespace RecordFerrers

namespace Skeleton

/-- `Σ (1-carry)` を整数で読むための defect 総量。 -/
def carryDefectSumFrom (start : ℕ) (rs : List ℕ) : ℤ :=
  (rs.length : ℤ) - (carrySumFrom start rs : ℤ)

/-- boundary excess は `Σ (1-carry)` と exact に一致する。 -/
theorem boundaryExcessInt_eq_sum_one_sub_carry
    (start : ℕ)
    (rs : List ℕ) :
    boundaryExcessInt start rs = carryDefectSumFrom start rs := by
  have hEx := boundaryExcessInt_eq_zeroCarryCountFrom start rs
  have hCount := carrySum_add_zeroCarryCount_eq_length start rs
  have hCountInt :
      (carrySumFrom start rs : ℤ) +
          (zeroCarryCountFrom start rs : ℤ) =
        (rs.length : ℤ) := by
    exact_mod_cast hCount
  unfold carryDefectSumFrom
  linarith

/-- full record skeleton では terminal までの excess は exact に 1。 -/
theorem boundaryExcessInt_eq_one_of_full
    (start : ℕ)
    (rs : List ℕ)
    (hCarry : carryConditionFrom start rs) :
    boundaryExcessInt start rs = 1 := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom,
      zeroCarryCount_eq_one_of_full start rs hCarry]
  norm_num

end Skeleton

end RecordFerrers
end Collatz2
