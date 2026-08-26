import CollatzLean.Collatz2.RecordFerrers.Perturbation.P09OneBitDefectLaw

/-!
# Record–Ferrers 摂動理論 10: 一度生じた excess の持続

carry 0 が一度 excess を 1 増やした後、後続 carry がすべて 1 なら excess は減らない。
raw carry の摂動が局所的でも、生成された roof offset は後方へ持続することを formalize する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- 指定 start 以後の全 block carry が 1 であること。空列は自明。 -/
def AllCarryOneFrom (start : ℕ) : List ℕ → Prop
  | [] => True
  | r :: rs =>
      criticalCarry start r = 1 ∧ AllCarryOneFrom (start + r) rs

/-- all-carry-one tail では zero carry は一つも現れない。 -/
theorem zeroCarryCountFrom_eq_zero_of_allCarryOne
    (start : ℕ)
    (rs : List ℕ)
    (h : AllCarryOneFrom start rs) :
    zeroCarryCountFrom start rs = 0 := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
      change
        criticalCarry start r = 1 ∧
          AllCarryOneFrom (start + r) rs at h
      simp [zeroCarryCountFrom, h.1, ih (start + r) h.2]

/-- zero-carry count は list append に対して start をずらして加法的。 -/
theorem zeroCarryCountFrom_append
    (start : ℕ)
    (xs ys : List ℕ) :
    zeroCarryCountFrom start (xs ++ ys) =
      zeroCarryCountFrom start xs +
        zeroCarryCountFrom (start + xs.sum) ys := by
  induction xs generalizing start with
  | nil =>
      simp [zeroCarryCountFrom]
  | cons r rs ih =>
      simp only [List.cons_append, List.sum_cons, zeroCarryCountFrom]
      rw [ih (start + r)]
      simp [Nat.add_assoc]

/-- all-carry-one tail を追加しても、すでにある boundary excess は変わらない。 -/
theorem boundaryExcessInt_append_eq_of_allCarryOne
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hTail : AllCarryOneFrom (start + leftCtx.sum) tail) :
    boundaryExcessInt start (leftCtx ++ tail) =
      boundaryExcessInt start leftCtx := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom,
      boundaryExcessInt_eq_zeroCarryCountFrom,
      zeroCarryCountFrom_append]
  rw [zeroCarryCountFrom_eq_zero_of_allCarryOne
    (start + leftCtx.sum) tail hTail]
  simp

/--
一個の defect により excess が 1 になった後、
後続 carry が 1 なら excess 1 は持続する。
-/
theorem persistent_excess_after_single_carry_failure
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hExcess : boundaryExcessInt start leftCtx = 1)
    (hTail : AllCarryOneFrom (start + leftCtx.sum) tail) :
    boundaryExcessInt start (leftCtx ++ tail) = 1 := by
  rw [boundaryExcessInt_append_eq_of_allCarryOne
    start leftCtx tail hTail]
  exact hExcess

end Skeleton

end RecordFerrers
end Collatz2
