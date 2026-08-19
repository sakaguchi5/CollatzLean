import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualCriticalFiniteScan
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongDenominatorWindowCover

/-!
# Public arithmetic wrappers for terminal-record arguments

既存 `ActualRhinStrongSlack.lean` 内部の private helper を外から参照しない。
terminal-record proof が必要とする denominator growth を、public theorem
`RhinLinearForm14.actual_q_next_le` だけからここで再証明し public API として公開する。

同時に actual corrected López--Stoll family / strong Xi match / H=4 height packetにも
名前を与える。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- actual corrected López--Stoll family。 -/
def actualRecordLopezStollInstantiation : LopezStollInstantiation :=
  actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket.toLopezStollInstantiation

@[simp] theorem actualRecordLopezStollInstantiation_q (j : ℕ) :
    actualRecordLopezStollInstantiation.q j = criticalPowerQ j := rfl

@[simp] theorem actualRecordLopezStollInstantiation_P (j : ℕ) :
    actualRecordLopezStollInstantiation.P j =
      correctedChristoffelP actualCriticalContinuedFractionData j := rfl

@[simp] theorem actualRecordLopezStollInstantiation_Q (j : ℕ) :
    actualRecordLopezStollInstantiation.Q j =
      correctedChristoffelQ actualCriticalContinuedFractionData j := rfl

/-- actual strong Xi matching の public wrapper。 -/
theorem actualRecordStrongBoundaryMatch :
    StrongBoundaryLopezStollMatch actualRecordLopezStollInstantiation := by
  have hI :=
    actualCriticalSturmianFiniteScanIdentity.toCriticalFiniteXiIdentity
  exact
    hI.toStrongBoundaryLopezStollMatch
      actualOrientedCriticalContinuedFractionData.toCriticalChristoffelPacket

/-- Rhin input から得る actual H=4 height packet。 -/
def actualRecordHeightFour
    (R : RhinLinearForm14) :
    ChristoffelHeightInstantiation actualRecordLopezStollInstantiation :=
  (actualCriticalASteps6to8 R).heightFour

@[simp] theorem actualRecordHeightFour_H
    (R : RhinLinearForm14) :
    (actualRecordHeightFour R).H = 4 := rfl

/-- actual strong window の最初の precision は 1538。 -/
theorem actualRecord_firstPrecision_eq_1538
    (R : RhinLinearForm14) :
    strongFirstPrecision actualRecordLopezStollInstantiation = 1538 := by
  simpa [actualRecordLopezStollInstantiation] using
    (actualCriticalASteps6to8 R).firstPrecision_eq_1538

/-- tail range `j>=12`: current denominator を previous denominator の14乗で抑える。 -/
theorem RhinLinearForm14.actual_record_current_q_le_prev_pow14
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    criticalPowerQ j ≤
      2 * criticalPowerQ (j - 1) ^ 14 := by
  have h := R.actual_q_next_le (j := j - 1) (by omega : 9 ≤ j - 1)
  simpa [show (j - 1) + 1 = j by omega] using h

/-- tail range `j>=12`: next denominator を previous denominator の196乗で抑える。 -/
theorem RhinLinearForm14.actual_record_next_q_le_prev_pow196
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    criticalPowerQ (j + 1) ≤
      2 ^ 15 * criticalPowerQ (j - 1) ^ 196 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  have hq : q ≤ 2 * n ^ 14 := by
    simpa [q, n] using R.actual_record_current_q_le_prev_pow14 hj
  have hNext :
      criticalPowerQ (j + 1) ≤ 2 * q ^ 14 := by
    simpa [q] using R.actual_q_next_le (j := j) (by omega : 9 ≤ j)
  have hPow : q ^ 14 ≤ (2 * n ^ 14) ^ 14 :=
    Nat.pow_le_pow_left hq 14
  calc
    criticalPowerQ (j + 1)
        ≤ 2 * q ^ 14 := hNext
    _ ≤ 2 * (2 * n ^ 14) ^ 14 := Nat.mul_le_mul_left 2 hPow
    _ = 2 ^ 15 * n ^ 196 := by
      rw [mul_pow, ← pow_mul]
      norm_num
      ring

/-- tail range `j>=12`: strong window upper endpoint は previous denominator の196乗。 -/
theorem RhinLinearForm14.actual_record_strongWindowUpper_add_two_le_prev_pow196
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    strongDenominatorWindowUpper criticalPowerQ j + 2 ≤
      2 ^ 17 * criticalPowerQ (j - 1) ^ 196 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  let qn := criticalPowerQ (j + 1)
  have hnPos : 0 < n := by
    dsimp [n]
    exact criticalPowerQ_pos _
  have hq : q ≤ 2 * n ^ 14 := by
    simpa [q, n] using R.actual_record_current_q_le_prev_pow14 hj
  have hqn : qn ≤ 2 ^ 15 * n ^ 196 := by
    simpa [qn, n] using R.actual_record_next_q_le_prev_pow196 hj
  have hnPow : n ^ 14 ≤ n ^ 196 :=
    Nat.pow_le_pow_right hnPos (by omega)
  have hq' : q ≤ 2 * n ^ 196 :=
    le_trans hq (Nat.mul_le_mul_left 2 hnPow)
  have hnOne : 1 ≤ n := by
    omega
  have hn196 : 1 ≤ n ^ 196 := by
    have := Nat.pow_le_pow_left hnOne 196
    simpa using this
  unfold strongDenominatorWindowUpper
  dsimp [q, qn, n] at hq' hqn hn196 ⊢
  omega

/-- `j>=12` なら strong upper endpoint 自身も同じ bound 以下。 -/
theorem RhinLinearForm14.actual_record_strongWindowUpper_le_prev_pow196
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    strongDenominatorWindowUpper criticalPowerQ j ≤
      2 ^ 17 * criticalPowerQ (j - 1) ^ 196 := by
  have h := R.actual_record_strongWindowUpper_add_two_le_prev_pow196 hj
  omega

end ExternalArithmetic
end CSTMicro
end Collatz2
