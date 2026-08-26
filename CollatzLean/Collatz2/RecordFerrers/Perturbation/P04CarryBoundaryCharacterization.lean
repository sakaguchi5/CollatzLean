import CollatzLean.Collatz2.RecordFerrers.Perturbation.P03BoundaryExcessClosedForm

/-!
# Record–Ferrers 摂動理論 4: carry 条件と境界 excess の同値

full record skeleton の再帰的 carry 条件を、各局所境界の excess 条件へ翻訳する。
interior block は excess 0、最後の block は excess 1 を作る。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/--
各 block を、その時点の critical roof を基準に読み直した局所 excess 条件。
最後だけ 1、それ以前は 0 を要求する。
-/
def boundaryExcessConditionFrom (start : ℕ) : List ℕ → Prop
  | [] => False
  | [r] => boundaryExcessInt start [r] = 1
  | r :: s :: rs =>
      boundaryExcessInt start [r] = 0 ∧
        boundaryExcessConditionFrom (start + r) (s :: rs)

/-- singleton excess 0 は carry 1 と同値。 -/
theorem boundaryExcessInt_singleton_eq_zero_iff
    (start r : ℕ) :
    boundaryExcessInt start [r] = 0 ↔ criticalCarry start r = 1 := by
  have hCases := criticalCarry_eq_zero_or_one start r
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  rcases hCases with hZero | hOne
  · rw [hZero]
    simp [zeroCarryCountFrom]
    omega
  · rw [hOne]
    simp [zeroCarryCountFrom]
    omega

/-- singleton excess 1 は carry 0 と同値。 -/
theorem boundaryExcessInt_singleton_eq_one_iff
    (start r : ℕ) :
    boundaryExcessInt start [r] = 1 ↔ criticalCarry start r = 0 := by
  have hCases := criticalCarry_eq_zero_or_one start r
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  rcases hCases with hZero | hOne
  · rw [hZero]
    simp [zeroCarryCountFrom]
    omega
  · rw [hOne]
    simp [zeroCarryCountFrom]
    omega

/-- full carry condition と局所 boundary excess 条件は exact に同値。 -/
theorem carryConditionFrom_iff_boundaryExcessConditionFrom
    (start : ℕ)
    (rs : List ℕ) :
    carryConditionFrom start rs ↔ boundaryExcessConditionFrom start rs := by
  induction rs generalizing start with
  | nil =>
      simp [carryConditionFrom, boundaryExcessConditionFrom]
  | cons r rs ih =>
      cases rs with
      | nil =>
          simpa [carryConditionFrom, boundaryExcessConditionFrom] using
            (boundaryExcessInt_singleton_eq_one_iff start r).symm
      | cons s ss =>
          change
            (criticalCarry start r = 1 ∧
              carryConditionFrom (start + r) (s :: ss)) ↔
            (boundaryExcessInt start [r] = 0 ∧
              boundaryExcessConditionFrom (start + r) (s :: ss))
          rw [boundaryExcessInt_singleton_eq_zero_iff]
          rw [ih (start + r)]

end Skeleton

end RecordFerrers
end Collatz2
