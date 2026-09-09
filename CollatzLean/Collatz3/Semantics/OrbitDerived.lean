import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum


/-!
# Collatz3: repeat / periodicity / future minimum の派生定理

`OddOrbit` の primitive data を増やさず、repeated state から値列だけでなく
指数列・有限 segment word の周期性まで導く。
また周期枝の長い tail-minimum 証明から、`1` 非自明性を使わない一般 repeat 補題を抽出する。
-/

namespace Collatz3
namespace OddOrbit

/--
時刻 `i<j` で同じ値に戻ったなら、値列だけでなく odd-only exponent 列も
幅 `j-i` で pointwise に周期的。
-/
theorem exponent_add_period_eq_of_repeat
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    ∀ q : ℕ,
      O.exponent (i + q + (j - i)) = O.exponent (i + q) := by
  intro q
  have hValue := O.value_add_period_eq_of_repeat hij heq q
  have hFuture := O.step (i + q + (j - i))
  have hCurrent := O.step (i + q)
  rw [hValue] at hFuture
  exact (OddStep.deterministic hFuture hCurrent).1

/--
repeat 開始以後の任意の shift から切り出した有限 exponent segment は、
一周期だけ右へずらしても exact に同じ word。
-/
theorem segmentWord_shift_period_eq_of_repeat
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    ∀ shift q : ℕ,
      O.segmentWord (i + shift + (j - i)) q =
        O.segmentWord (i + shift) q := by
  intro shift q
  induction q generalizing shift with
  | zero =>
      rfl
  | succ q ih =>
      rw [O.segmentWord_succ, O.segmentWord_succ]
      have hHead :=
        O.exponent_add_period_eq_of_repeat hij heq shift
      have hTail :
          O.segmentWord ((i + shift + (j - i)) + 1) q =
            O.segmentWord ((i + shift) + 1) q := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (ih (shift + 1))
      rw [hHead, hTail]

/-- repeat 基点そのものから切り出す finite word の一周期 shift 不変性。 -/
theorem segmentWord_add_period_eq_of_repeat
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j)
    (q : ℕ) :
    O.segmentWord (i + (j - i)) q = O.segmentWord i q := by
  simpa using O.segmentWord_shift_period_eq_of_repeat hij heq 0 q

/--
repeated state が与える `[i,j)` segment は、その基点への actual nonempty return そのもの。
同じ return segment の再構成を各 proof で繰り返さないための共通 bridge。
-/
theorem returnsTo_segmentWord_of_repeat
    (O : OddOrbit)
    {i j : ℕ}
    (hij : i < j)
    (heq : O.value i = O.value j) :
    ReturnsTo (O.segmentWord i (j - i)) (O.value i) := by
  have hLenPos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hNonempty : O.segmentWord i (j - i) ≠ [] := by
    intro hNil
    have hLen := O.segmentWord_oddSteps i (j - i)
    rw [hNil] at hLen
    simp at hLen
    omega
  have hRun := O.runsSegment i (j - i)
  have hIndex : i + (j - i) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hij)
  rw [hIndex, ← heq] at hRun
  exact ⟨hNonempty, hRun⟩

/--
第2分類 `HasNontrivialRepeat` は、開始値から到達可能な非自明 primitive periodic orbit が
存在することと exact に同値。
-/
theorem hasNontrivialRepeat_iff_exists_eventual_nontrivialPeriodicOrbit
    (O : OddOrbit) :
    O.HasNontrivialRepeat ↔
      ∃ i : ℕ, ∃ w : Word,
        Reaches (O.value 0) (O.value i) ∧
          IsNontrivialPeriodicOrbit w (O.value i) := by
  constructor
  · exact O.exists_eventual_nontrivialPeriodicOrbit_of_repeat
  · rintro ⟨i, w, _hReach, hPeriodic⟩
    let q : ℕ := Word.oddSteps w
    have hqPos : 0 < q := by
      have hne := hPeriodic.1.returnsTo.word_nonempty
      cases w with
      | nil => contradiction
      | cons e ws =>
          simp [q, Word.oddSteps]
    have hReturn : Runs w (O.value i) (O.value i) :=
      hPeriodic.1.returnsTo.run
    have hActual := O.runsSegment i q
    have hSameLength :
        Word.oddSteps w = Word.oddSteps (O.segmentWord i q) := by
      simp [q]
    have hDet :=
      Runs.word_end_eq_of_common_start_same_oddSteps
        hReturn hActual hSameLength
    refine ⟨i, i + q, ?_, hDet.2, hPeriodic.2⟩
    omega

end OddOrbit
end Collatz3
