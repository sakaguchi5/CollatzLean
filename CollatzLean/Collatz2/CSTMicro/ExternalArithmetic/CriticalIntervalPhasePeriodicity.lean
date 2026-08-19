import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyCurrentCorridor

/-!
# Stage 8B.2: shifted critical interval の exact phase periodicity

Stage 8B.1 の Beatty floor corridor を interval numerator / gap / affine defect に持ち上げる。

odd scale では origin を含めて P-periodic。
even scale では origin だけ first-flat であり、positive domain `[1,...)` では P-periodic。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- `Ico a (a+n)` を local offset range へ移す。 -/
private theorem stage8_sum_Ico_eq_sum_range
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    (a n : ℕ) :
    Finset.sum (Finset.Ico a (a + n)) f =
      Finset.sum (Finset.range n) (fun i => f (a + i)) := by
  symm
  refine Finset.sum_bij (fun i _ => a + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hiLt : i < n := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ hEq
    omega
  · intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    refine ⟨k - a, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

/-- one-cell interval numerator is exactly one. -/
theorem criticalIntervalPhiZ_step_eq_one_stage8
    (a : ℕ) :
    criticalIntervalPhiZ a (a + 1) = 1 := by
  unfold criticalIntervalPhiZ
  rw [stage8_sum_Ico_eq_sum_range
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex a) *
        (3 : ℤ) ^ (a + 1 - 1 - k)) a 1]
  simp

/-- critical prefix numerator at one is one. -/
theorem criticalPrefixPhiZ_one_stage8 :
    criticalPrefixPhiZ 1 = 1 := by
  rw [criticalPrefixPhiZ_eq_interval_zero]
  simpa using criticalIntervalPhiZ_step_eq_one_stage8 0

theorem criticalIntervalPhiZ_shift_currentP_eq_of_odd
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1)) :
    criticalIntervalPhiZ
        (criticalPowerP j) (criticalPowerP j + l) =
      criticalIntervalPhiZ 0 l := by
  unfold criticalIntervalPhiZ
  rw [stage8_sum_Ico_eq_sum_range
    (fun k =>
      (2 : ℤ) ^
          (beattyIndex k - beattyIndex (criticalPowerP j)) *
        (3 : ℤ) ^ (criticalPowerP j + l - 1 - k))
    (criticalPowerP j) l]
  have hZeroRange :
      Finset.sum (Finset.Ico 0 l)
          (fun k =>
            (2 : ℤ) ^ (beattyIndex k - beattyIndex 0) *
              (3 : ℤ) ^ (l - 1 - k)) =
        Finset.sum (Finset.range l)
          (fun i =>
            (2 : ℤ) ^ (beattyIndex i - beattyIndex 0) *
              (3 : ℤ) ^ (l - 1 - i)) := by
    simpa only [Nat.zero_add] using
      (stage8_sum_Ico_eq_sum_range
        (fun k =>
          (2 : ℤ) ^ (beattyIndex k - beattyIndex 0) *
            (3 : ℤ) ^ (l - 1 - k))
        0 l)
  rw [hZeroRange]
  apply Finset.sum_congr rfl
  intro i hi
  have hiLt : i < l := Finset.mem_range.mp hi
  have hShift :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_odd
      hj hjOdd
      (by omega :
        criticalPowerP j + i < criticalPowerP (j + 1))
  have hBase :=
    actual_beattyIndex_currentP_eq_Q_of_odd hj hjOdd
  have hThree :
      criticalPowerP j + l - 1 - (criticalPowerP j + i) =
        l - 1 - i := by
    omega
  simp only [ beattyIndex_zero, tsub_zero]
  rw [hShift, hBase, hThree]
  have hBeta :
      criticalPowerQ j + beattyIndex i - criticalPowerQ j =
        beattyIndex i := by
    omega
  rw [hBeta]

/-- odd scale: gap is exactly P-periodic. -/
theorem criticalIntervalGapZ_shift_currentP_eq_of_odd
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1)) :
    criticalIntervalGapZ
        (criticalPowerP j) (criticalPowerP j + l) =
      criticalIntervalGapZ 0 l := by
  have hShift :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_odd hj hjOdd hRange
  have hBase := actual_beattyIndex_currentP_eq_Q_of_odd hj hjOdd
  unfold criticalIntervalGapZ
  simp only [beattyIndex_zero, tsub_zero, Nat.add_sub_cancel_left]
  rw [hShift, hBase]
  have hBeta :
      criticalPowerQ j + beattyIndex l - criticalPowerQ j =
        beattyIndex l := by omega
  rw [hBeta]

/-- odd scale: affine defect is exactly P-periodic. -/
theorem criticalIntervalDefectZ_shift_currentP_eq_of_odd
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1))
    (y : ℤ) :
    criticalIntervalDefectZ
        (criticalPowerP j) (criticalPowerP j + l) y =
      criticalIntervalDefectZ 0 l y := by
  unfold criticalIntervalDefectZ
  rw [criticalIntervalPhiZ_shift_currentP_eq_of_odd hj hjOdd hRange]
  rw [criticalIntervalGapZ_shift_currentP_eq_of_odd hj hjOdd hRange]

/-- even scale: positive-domain numerator is exactly P-periodic. -/
theorem criticalIntervalPhiZ_shift_currentP_pos_eq_of_even
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hl : 1 ≤ l)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1)) :
    criticalIntervalPhiZ
        (criticalPowerP j + 1) (criticalPowerP j + l) =
      criticalIntervalPhiZ 1 l := by
  let n := l - 1
  have hLn : l = 1 + n := by
    dsimp [n]
    omega
  unfold criticalIntervalPhiZ
  rw [hLn]
  have hCurrentRange :
      Finset.sum
          (Finset.Ico
            (criticalPowerP j + 1)
            (criticalPowerP j + (1 + n)))
          (fun k =>
            (2 : ℤ) ^
                (beattyIndex k -
                  beattyIndex (criticalPowerP j + 1)) *
              (3 : ℤ) ^
                (criticalPowerP j + (1 + n) - 1 - k)) =
        Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^
                (beattyIndex (criticalPowerP j + 1 + i) -
                  beattyIndex (criticalPowerP j + 1)) *
              (3 : ℤ) ^
                (criticalPowerP j + (1 + n) - 1 -
                  (criticalPowerP j + 1 + i))) := by
    simpa only [Nat.add_assoc] using
      (stage8_sum_Ico_eq_sum_range
        (fun k =>
          (2 : ℤ) ^
              (beattyIndex k -
                beattyIndex (criticalPowerP j + 1)) *
            (3 : ℤ) ^
              (criticalPowerP j + (1 + n) - 1 - k))
        (criticalPowerP j + 1) n)
  rw [hCurrentRange]
  have hBaseRange :
      Finset.sum (Finset.Ico 1 (1 + n))
          (fun k =>
            (2 : ℤ) ^ (beattyIndex k - beattyIndex 1) *
              (3 : ℤ) ^ (1 + n - 1 - k)) =
        Finset.sum (Finset.range n)
          (fun i =>
            (2 : ℤ) ^
                (beattyIndex (1 + i) - beattyIndex 1) *
              (3 : ℤ) ^
                (1 + n - 1 - (1 + i))) := by
    exact
      stage8_sum_Ico_eq_sum_range
        (fun k =>
          (2 : ℤ) ^ (beattyIndex k - beattyIndex 1) *
            (3 : ℤ) ^ (1 + n - 1 - k))
        1 n
  rw [hBaseRange]
  apply Finset.sum_congr rfl
  intro i hi
  have hiLt : i < n := Finset.mem_range.mp hi
  have hShiftI0 :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      hj hjEven
      (by omega : 0 < 1 + i)
      (by omega :
        criticalPowerP j + (1 + i) <
          criticalPowerP (j + 1))
  have hShiftI :
      beattyIndex (criticalPowerP j + 1 + i) =
        criticalPowerQ j + beattyIndex (1 + i) := by
    simpa [Nat.add_assoc] using hShiftI0
  have hShiftOne :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      hj hjEven
      (by omega : 0 < 1)
      (by omega :
        criticalPowerP j + 1 <
          criticalPowerP (j + 1))
  have hThree :
      criticalPowerP j + (1 + n) - 1 -
          (criticalPowerP j + 1 + i) =
        1 + n - 1 - (1 + i) := by
    omega
  rw [hShiftI, hShiftOne, hThree]
  have hBeta :
      criticalPowerQ j + beattyIndex (1 + i) -
          (criticalPowerQ j + beattyIndex 1) =
        beattyIndex (1 + i) - beattyIndex 1 := by
    omega
  rw [hBeta]

/-- even scale: positive-domain gap is P-periodic. -/
theorem criticalIntervalGapZ_shift_currentP_pos_eq_of_even
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hl : 1 ≤ l)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1)) :
    criticalIntervalGapZ
        (criticalPowerP j + 1) (criticalPowerP j + l) =
      criticalIntervalGapZ 1 l := by
  have hShiftL :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      hj hjEven (by omega : 0 < l) hRange
  have hShiftOne :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      hj hjEven (by omega : 0 < 1)
      (by omega : criticalPowerP j + 1 < criticalPowerP (j + 1))
  unfold criticalIntervalGapZ
  rw [hShiftL, hShiftOne]
  have hBeta :
      criticalPowerQ j + beattyIndex l -
          (criticalPowerQ j + beattyIndex 1) =
        beattyIndex l - beattyIndex 1 := by omega
  have hLen :
      criticalPowerP j + l - (criticalPowerP j + 1) = l - 1 := by omega
  rw [hBeta, hLen]

/-- even scale: positive-domain affine defect is P-periodic. -/
theorem criticalIntervalDefectZ_shift_currentP_pos_eq_of_even
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hl : 1 ≤ l)
    (hRange : criticalPowerP j + l < criticalPowerP (j + 1))
    (y : ℤ) :
    criticalIntervalDefectZ
        (criticalPowerP j + 1) (criticalPowerP j + l) y =
      criticalIntervalDefectZ 1 l y := by
  unfold criticalIntervalDefectZ
  rw [criticalIntervalPhiZ_shift_currentP_pos_eq_of_even
    hj hjEven hl hRange]
  rw [criticalIntervalGapZ_shift_currentP_pos_eq_of_even
    hj hjEven hl hRange]

end ExternalArithmetic
end CSTMicro
end Collatz2
