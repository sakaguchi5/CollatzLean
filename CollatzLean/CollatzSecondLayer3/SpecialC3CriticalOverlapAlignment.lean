import CollatzLean.CollatzSecondLayer3.SpecialC3TransportedCollision
import CollatzLean.CollatzFirstLayer.SignedCommonWordDivisibility

/-!
# 増加terminal overlapのcritical one-bit alignment

terminal time狭義増加部分列で二つのSpecial C3 source intervalが重なる場合、
startだけでなくlengthも増加するため、左intervalのendが先に来る。
したがって共通actual segmentは左seedのtail全体であり、右seedではproper prefixになる。

右seedの残りsuffixを`rightRemainderWord`として明示すると、共通wordの総2進depthを`H`、
右suffixの総2進depthを`S`、start間offsetを`d`として、

`right center - transported left center
   = 2^(H+1) * (3^d - 2^S)`

を得る。`S > 0`なので括弧内は奇数である。
さらに二signed状態を共通actual wordで輸送すると、

`right finish - left finish
   = 2 * 3^L * (3^d - 2^S)`

となる。したがって共通wordが`H`ビットを消費した直後には、
差の2進depthがexactに1だけ残る。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/--
shadow wordのcanonical開始値は、保存されたnegative centerにresidue幅を一つ足したもの。
center保存とcanonical representativeを往復するための基本API。
-/
theorem canonicalStart_shadowWord_eq_center_add_modulus
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    (canonicalStart (R.shadowWord j n) : ℤ) =
      R.center j + (residueModulus (R.shadowWord j n) : ℤ) := by
  have h := R.predecessorStart_shadowWord_eq_center j n
  unfold predecessorStart at h
  omega

/--
terminal time増加部分列ではstartとlengthが同時に増えるのでsource interval endも狭義増加する。
-/
theorem sourceIntervalEnd_strict_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime) :
    StrictMono (fun n => R.sourceIntervalEnd (S.select n)) := by
  intro a b hab
  have hStart :
      R.start (S.select a) < R.start (S.select b) :=
    R.start_strict_on_increasingTerminalSubsequence S hab
  have hLength :
      R.length (S.select a) < R.length (S.select b) :=
    R.length_strict_on_increasingTerminalSubsequence S hab
  unfold sourceIntervalEnd
  exact Nat.add_lt_add hStart hLength

/--
増加terminal部分列のoverlapでは左intervalのendが先なので、overlap長は左tail長に一致する。
-/
theorem overlapLength_eq_leftTailLength_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.overlapLength (S.select n) (S.select (n + 1)) =
      R.leftTailLength (S.select n) (S.select (n + 1)) := by
  have hEnd :
      R.sourceIntervalEnd (S.select n) <
        R.sourceIntervalEnd (S.select (n + 1)) :=
    R.sourceIntervalEnd_strict_on_increasingTerminalSubsequence S
      (Nat.lt_succ_self n)
  have hMin :
      min
          (R.sourceIntervalEnd (S.select n))
          (R.sourceIntervalEnd (S.select (n + 1))) =
        R.sourceIntervalEnd (S.select n) :=
    min_eq_left (Nat.le_of_lt hEnd)
  have hStart :
      R.start (S.select n) < R.start (S.select (n + 1)) :=
    R.start_strict_on_increasingTerminalSubsequence S
      (Nat.lt_succ_self n)
  have hInside := hOverlap.2
  unfold sourceIntervalStart sourceIntervalEnd at hInside
  unfold overlapLength
  rw [hMin]
  unfold leftTailLength overlapOffset sourceIntervalEnd
  omega

/-- 増加terminal overlapの共通wordは左seedのtail全体そのもの。 -/
theorem overlapWord_eq_leftTailWord_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.overlapWord (S.select n) (S.select (n + 1)) =
      R.leftTailWord (S.select n) (S.select (n + 1)) := by
  have hLength :=
    R.overlapLength_eq_leftTailLength_on_increasingTerminalSubsequence
      S n hOverlap
  unfold overlapWord leftTailWord
  rw [hLength]

/-- 増加terminal overlapでは共通wordは右seedのproper prefix長を持つ。 -/
theorem overlapLength_lt_right_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.overlapLength (S.select n) (S.select (n + 1)) <
      R.length (S.select (n + 1)) := by
  have hLengthEq :=
    R.overlapLength_eq_leftTailLength_on_increasingTerminalSubsequence
      S n hOverlap
  have hLength :
      R.length (S.select n) <
        R.length (S.select (n + 1)) :=
    R.length_strict_on_increasingTerminalSubsequence
      S
      (Nat.lt_succ_self n)
  rw [hLengthEq]
  calc
    R.leftTailLength (S.select n) (S.select (n + 1))
        ≤ R.length (S.select n) := by
          unfold leftTailLength
          exact Nat.sub_le _ _
    _ < R.length (S.select (n + 1)) := hLength

/-- 共通word終了後に右seed側へ残る長さ。 -/
def rightRemainderLength
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℕ :=
  R.length k - R.overlapLength j k

/-- 共通word終了後に右seed側へ残るactual suffix word。 -/
def rightRemainderWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ExpWord :=
  O.segmentWord
    (R.start k + R.overlapLength j k)
    (R.rightRemainderLength j k)

/-- 右seed wordを共通wordと残りsuffixへ分解する。 -/
theorem word_eq_overlap_append_rightRemainder
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hOverlap : R.SourceIntervalsOverlap j k) :
    R.word k =
      R.overlapWord j k ++ R.rightRemainderWord j k := by
  have hLe := R.overlapLength_le_right hOverlap
  have hLength :
      R.length k =
        R.overlapLength j k + R.rightRemainderLength j k := by
    unfold rightRemainderLength
    omega
  unfold word overlapWord rightRemainderWord
  rw [hLength]
  rw [O.segmentWord_add]

/-- 右seed総2進depthは共通wordと残りsuffixのdepthの和。 -/
theorem word_twoSteps_eq_overlap_add_rightRemainder
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hOverlap : R.SourceIntervalsOverlap j k) :
    twoSteps (R.word k) =
      twoSteps (R.overlapWord j k) +
        twoSteps (R.rightRemainderWord j k) := by
  rw [R.word_eq_overlap_append_rightRemainder hOverlap]
  rw [twoSteps_append]

/-- 増加terminal overlapでは右suffix長は正。 -/
theorem rightRemainderLength_pos_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    0 < R.rightRemainderLength (S.select n) (S.select (n + 1)) := by
  have hLt :=
    R.overlapLength_lt_right_on_increasingTerminalSubsequence
      S n hOverlap
  unfold rightRemainderLength
  omega

/-- 増加terminal overlapでは右suffix wordは非空。 -/
theorem rightRemainderWord_ne_nil_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.rightRemainderWord (S.select n) (S.select (n + 1)) ≠ [] := by
  intro hNil
  have hOddSteps :
      oddSteps
          (R.rightRemainderWord (S.select n) (S.select (n + 1))) =
        R.rightRemainderLength (S.select n) (S.select (n + 1)) := by
    simp [rightRemainderWord, oddSteps]
  rw [hNil] at hOddSteps
  have hPos :=
    R.rightRemainderLength_pos_on_increasingTerminalSubsequence
      S n hOverlap
  simp [oddSteps] at hOddSteps
  omega

/-- 右suffixはactual orbitから切り出した正指数語。 -/
theorem rightRemainderWord_valid
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    Valid (R.rightRemainderWord j k) := by
  unfold rightRemainderWord
  exact
    (O.runs_segment
      (R.start k + R.overlapLength j k)
      (R.rightRemainderLength j k)).valid

/-- 増加terminal overlapでは右suffixが消費する2進depthは正。 -/
theorem rightRemainderTwoSteps_pos_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    0 < twoSteps
      (R.rightRemainderWord (S.select n) (S.select (n + 1))) := by
  exact
    twoSteps_pos_of_valid_nonempty
      (R.rightRemainderWord_valid (S.select n) (S.select (n + 1)))
      (R.rightRemainderWord_ne_nil_on_increasingTerminalSubsequence
        S n hOverlap)

/-- 増加overlapで現れる開始差のodd kernel。 -/
def criticalOddKernel
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℤ :=
  (3 : ℤ) ^ R.overlapOffset j k -
    (2 : ℤ) ^ twoSteps (R.rightRemainderWord j k)

private theorem odd_three_pow_int (m : ℕ) : Odd ((3 : ℤ) ^ m) := by
  induction m with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ m ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨3 * u + 1, ?_⟩
      rw [pow_succ, hu]
      ring

private theorem even_two_pow_int_of_pos
    {m : ℕ}
    (hm : 0 < m) :
    Even ((2 : ℤ) ^ m) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m = r + 1 :=
    ⟨m - 1, by omega⟩
  refine ⟨(2 : ℤ) ^ r, ?_⟩
  rw [hr, pow_succ]
  ring

private theorem odd_mul_int
    {a b : ℤ}
    (ha : Odd a)
    (hb : Odd b) :
    Odd (a * b) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  refine ⟨2 * u * v + u + v, ?_⟩
  rw [hu, hv]
  ring

/-- critical kernelは奇数。 -/
theorem criticalOddKernel_odd_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    Odd (R.criticalOddKernel (S.select n) (S.select (n + 1))) := by
  have hTwoPos :=
    R.rightRemainderTwoSteps_pos_on_increasingTerminalSubsequence
      S n hOverlap
  unfold criticalOddKernel
  exact
    (odd_three_pow_int
      (R.overlapOffset (S.select n) (S.select (n + 1)))).sub_even
      (even_two_pow_int_of_pos hTwoPos)

/-- 左から輸送したcenterを共通wordのresidue幅で書く。 -/
theorem transportedCenterFromLeft_eq_critical_start
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.transportedCenterFromLeft (S.select n) (S.select (n + 1)) =
      (O.value (R.start (S.select (n + 1))) : ℤ) -
        (2 : ℤ) ^
            (twoSteps
                (R.overlapWord (S.select n) (S.select (n + 1))) + 1) *
          (3 : ℤ) ^
            R.overlapOffset (S.select n) (S.select (n + 1)) := by
  have hWord :=
    R.overlapWord_eq_leftTailWord_on_increasingTerminalSubsequence
      S n hOverlap
  unfold transportedCenterFromLeft
  rw [← hWord]
  ring

/-- 右seed centerを共通word幅×右suffix幅として書く。 -/
theorem rightCenter_eq_critical_start
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.center (S.select (n + 1)) =
      (O.value (R.start (S.select (n + 1))) : ℤ) -
        (2 : ℤ) ^
            (twoSteps
                (R.overlapWord (S.select n) (S.select (n + 1))) + 1) *
          (2 : ℤ) ^
            twoSteps
              (R.rightRemainderWord (S.select n) (S.select (n + 1))) := by
  rw [R.center_eq_actual_sub_twoPow (S.select (n + 1))]
  rw [R.word_twoSteps_eq_overlap_add_rightRemainder hOverlap]
  rw [show
    twoSteps (R.overlapWord (S.select n) (S.select (n + 1))) +
          twoSteps (R.rightRemainderWord (S.select n) (S.select (n + 1))) + 1 =
      (twoSteps (R.overlapWord (S.select n) (S.select (n + 1))) + 1) +
        twoSteps (R.rightRemainderWord (S.select n) (S.select (n + 1))) by
          omega]
  rw [pow_add]

/--
増加overlap開始位置での二signed center差は、共通wordのresidue幅×奇数kernelにexact分解される。
-/
theorem criticalStartDifference_factorization
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.center (S.select (n + 1)) -
        R.transportedCenterFromLeft (S.select n) (S.select (n + 1)) =
      (2 : ℤ) ^
          (twoSteps
              (R.overlapWord (S.select n) (S.select (n + 1))) + 1) *
        R.criticalOddKernel (S.select n) (S.select (n + 1)) := by
  rw [R.rightCenter_eq_critical_start S n hOverlap]
  rw [R.transportedCenterFromLeft_eq_critical_start S n hOverlap]
  unfold criticalOddKernel
  ring

/-- 左輸送状態を共通actual wordで走らせたsigned終点。 -/
def leftOverlapTransportFinish
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℤ :=
  (O.value (R.start k + R.overlapLength j k) : ℤ) -
    2 * (3 : ℤ) ^ oddSteps (R.overlapWord j k) *
      (3 : ℤ) ^ R.overlapOffset j k

/-- 右seed centerを共通actual wordで走らせたsigned終点。 -/
def rightOverlapTransportFinish
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℤ :=
  (O.value (R.start k + R.overlapLength j k) : ℤ) -
    2 * (3 : ℤ) ^ oddSteps (R.overlapWord j k) *
      (2 : ℤ) ^ twoSteps (R.rightRemainderWord j k)

/-- 左輸送centerは共通wordを上記signed終点まで実現する。 -/
theorem leftOverlapTransport_realizesInt
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    RealizesInt
      (R.overlapWord (S.select n) (S.select (n + 1)))
      (R.transportedCenterFromLeft (S.select n) (S.select (n + 1)))
      (R.leftOverlapTransportFinish (S.select n) (S.select (n + 1))) := by
  have hActual :=
    (R.overlapWord_realizes (S.select n) (S.select (n + 1))).toInt
  have hShift :=
    realizesInt_sub_replay hActual
      ((3 : ℤ) ^ R.overlapOffset (S.select n) (S.select (n + 1)))
  rw [residueModulus_int_cast] at hShift
  have hStartEq :=
    R.transportedCenterFromLeft_eq_critical_start S n hOverlap
  rw [← hStartEq] at hShift
  simpa [leftOverlapTransportFinish] using hShift

/-- 右seed centerも同じ共通wordを上記signed終点まで実現する。 -/
theorem rightOverlapTransport_realizesInt
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    RealizesInt
      (R.overlapWord (S.select n) (S.select (n + 1)))
      (R.center (S.select (n + 1)))
      (R.rightOverlapTransportFinish (S.select n) (S.select (n + 1))) := by
  have hActual :=
    (R.overlapWord_realizes (S.select n) (S.select (n + 1))).toInt
  have hShift :=
    realizesInt_sub_replay hActual
      ((2 : ℤ) ^
        twoSteps
          (R.rightRemainderWord (S.select n) (S.select (n + 1))))
  rw [residueModulus_int_cast] at hShift
  have hStartEq :=
    R.rightCenter_eq_critical_start S n hOverlap
  rw [← hStartEq] at hShift
  simpa [rightOverlapTransportFinish] using hShift

/-- 共通word輸送後の差のodd kernel。 -/
def criticalFinishKernel
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℤ :=
  (3 : ℤ) ^ oddSteps (R.overlapWord j k) *
    R.criticalOddKernel j k

/-- 共通word輸送後の差は`2 * 3^L * criticalOddKernel`。 -/
theorem overlapTransport_finish_difference
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    R.rightOverlapTransportFinish j k -
        R.leftOverlapTransportFinish j k =
      2 * R.criticalFinishKernel j k := by
  unfold rightOverlapTransportFinish leftOverlapTransportFinish
    criticalFinishKernel criticalOddKernel
  ring

/-- 増加overlapではfinish側kernelも奇数。 -/
theorem criticalFinishKernel_odd_on_increasingTerminalSubsequence
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    Odd (R.criticalFinishKernel (S.select n) (S.select (n + 1))) := by
  unfold criticalFinishKernel
  exact
    odd_mul_int
      (odd_three_pow_int
        (oddSteps (R.overlapWord (S.select n) (S.select (n + 1)))))
      (R.criticalOddKernel_odd_on_increasingTerminalSubsequence
        S n hOverlap)

/--
増加overlapでは共通word輸送後のsigned差はexactに`2 * odd`。
すなわち共通wordが開始時の`H+1` alignmentのうち`H`を消費し、1ビットだけ残す。
-/
theorem overlapTransport_finish_exact_one_bit
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    R.rightOverlapTransportFinish (S.select n) (S.select (n + 1)) -
          R.leftOverlapTransportFinish (S.select n) (S.select (n + 1)) =
        2 * R.criticalFinishKernel (S.select n) (S.select (n + 1)) ∧
      Odd (R.criticalFinishKernel (S.select n) (S.select (n + 1))) := by
  constructor
  · exact R.overlapTransport_finish_difference _ _
  · exact
      R.criticalFinishKernel_odd_on_increasingTerminalSubsequence
        S n hOverlap

/--
一つの増加terminal overlap pairについて、critical alignmentに必要な情報をまとめる。
-/
structure CriticalOverlapAlignmentData
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ) where
  overlap :
    R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))
  startKernel : ℤ
  startKernel_odd : Odd startKernel
  startDifference :
    R.center (S.select (n + 1)) -
        R.transportedCenterFromLeft (S.select n) (S.select (n + 1)) =
      (2 : ℤ) ^
          (twoSteps
              (R.overlapWord (S.select n) (S.select (n + 1))) + 1) *
        startKernel
  leftRealizes :
    RealizesInt
      (R.overlapWord (S.select n) (S.select (n + 1)))
      (R.transportedCenterFromLeft (S.select n) (S.select (n + 1)))
      (R.leftOverlapTransportFinish (S.select n) (S.select (n + 1)))
  rightRealizes :
    RealizesInt
      (R.overlapWord (S.select n) (S.select (n + 1)))
      (R.center (S.select (n + 1)))
      (R.rightOverlapTransportFinish (S.select n) (S.select (n + 1)))
  finishKernel : ℤ
  finishKernel_odd : Odd finishKernel
  finishDifference :
    R.rightOverlapTransportFinish (S.select n) (S.select (n + 1)) -
        R.leftOverlapTransportFinish (S.select n) (S.select (n + 1)) =
      2 * finishKernel

/-- overlap仮定からcritical one-bit alignment dataを自動構成する。 -/
noncomputable def criticalOverlapAlignmentData
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (S : IncreasingNatSubsequenceData R.terminalTime)
    (n : ℕ)
    (hOverlap :
      R.SourceIntervalsOverlap (S.select n) (S.select (n + 1))) :
    CriticalOverlapAlignmentData R S n where
  overlap := hOverlap
  startKernel := R.criticalOddKernel (S.select n) (S.select (n + 1))
  startKernel_odd :=
    R.criticalOddKernel_odd_on_increasingTerminalSubsequence S n hOverlap
  startDifference :=
    R.criticalStartDifference_factorization S n hOverlap
  leftRealizes :=
    R.leftOverlapTransport_realizesInt S n hOverlap
  rightRealizes :=
    R.rightOverlapTransport_realizesInt S n hOverlap
  finishKernel := R.criticalFinishKernel (S.select n) (S.select (n + 1))
  finishKernel_odd :=
    R.criticalFinishKernel_odd_on_increasingTerminalSubsequence S n hOverlap
  finishDifference :=
    R.overlapTransport_finish_difference (S.select n) (S.select (n + 1))

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
