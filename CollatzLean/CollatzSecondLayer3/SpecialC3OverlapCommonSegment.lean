import CollatzLean.CollatzSecondLayer3.SpecialC3IntervalSubsequence

/-!
# Special C3 source interval overlapから共通actual segmentを抽出

二つのsource intervalが重なり、左側seedのstartが右側seedのstart以下なら、
共通部分をactual orbitの同一`segmentWord`として取り出す。
左wordではdrop後のprefix、右wordではprefixそのものとして現れる。
-/

namespace CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 長いsegment wordの先頭`m`文字をdropすると、残りのactual segmentになる。 -/
theorem segmentWord_drop_of_le
    (O : OddOrbit) {i m n : ℕ}
    (h : m ≤ n) :
    (O.segmentWord i n).drop m =
      O.segmentWord (i + m) (n - m) := by
  induction m generalizing i n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          have hm : m ≤ n := by omega
          simp only [segmentWord_succ, List.drop_succ_cons]
          have hrec := ih (i := i + 1) (n := n) hm
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

end OddOrbit
end CollatzCore

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- 左seed startから右seed startまでのoffset。 -/
def overlapOffset
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℕ :=
  R.start k - R.start j

/-- 二intervalの共通部分長。左端は右seed startとする。 -/
def overlapLength
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℕ :=
  min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) - R.start k

/-- overlapから取り出すactual共通word。 -/
def overlapWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ExpWord :=
  O.segmentWord (R.start k) (R.overlapLength j k)

/-- start順序があるとoffsetで右seed startへexactに到達する。 -/
theorem start_add_overlapOffset
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k) :
    R.start j + R.overlapOffset j k = R.start k := by
  unfold overlapOffset
  omega

/-- 真のoverlapでは共通部分長は正。 -/
theorem overlapLength_pos
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (h : R.SourceIntervalsOverlap j k) :
    0 < R.overlapLength j k := by
  have hlen : 0 < R.length k := by
    simp [length]
  have hRightEnd : R.start k < R.sourceIntervalEnd k := by
    unfold sourceIntervalEnd
    omega
  have hMin :
      R.start k <
        min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) := by
    exact (lt_min_iff).2 ⟨h.2, hRightEnd⟩
  unfold overlapLength
  exact Nat.sub_pos_of_lt hMin

/-- 共通部分は右seed wordの長さ以内。 -/
theorem overlapLength_le_right
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (_h : R.SourceIntervalsOverlap j k) :
    R.overlapLength j k ≤ R.length k := by
  have hMin :
      min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) ≤
        R.sourceIntervalEnd k := min_le_right _ _
  unfold overlapLength sourceIntervalEnd at hMin ⊢
  omega

/-- 左offsetと共通長の和は左seed wordの長さ以内。 -/
theorem overlapOffset_add_length_le_left
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (hOverlap : R.SourceIntervalsOverlap j k) :
    R.overlapOffset j k + R.overlapLength j k ≤ R.length j := by
  have hStartEndJ :
      R.start k ≤ R.sourceIntervalEnd j := by
    have h := hOverlap.2
    unfold sourceIntervalStart at h
    exact Nat.le_of_lt h
  have hStartEndK :
      R.start k ≤ R.sourceIntervalEnd k := by
    unfold sourceIntervalEnd
    omega
  have hStartMin :
      R.start k ≤
        min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) := by
    exact le_min hStartEndJ hStartEndK
  have hOffsetExact :
      R.overlapOffset j k + R.start j =
        R.start k := by
    unfold overlapOffset
    exact Nat.sub_add_cancel hStart
  have hLengthExact :
      R.overlapLength j k + R.start k =
        min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) := by
    unfold overlapLength
    exact Nat.sub_add_cancel hStartMin
  have hMinLeft :
      min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) ≤
        R.sourceIntervalEnd j :=
    min_le_left _ _
  have hTotal :
      R.overlapOffset j k +
          R.overlapLength j k +
          R.start j ≤
        R.length j + R.start j := by
    calc
      R.overlapOffset j k +
            R.overlapLength j k +
            R.start j
          =
        R.overlapLength j k + R.start k := by
          rw [← hOffsetExact]
          ring
      _ =
        min (R.sourceIntervalEnd j) (R.sourceIntervalEnd k) :=
          hLengthExact
      _ ≤ R.sourceIntervalEnd j :=
        hMinLeft
      _ =
        R.length j + R.start j := by
          unfold sourceIntervalEnd
          ring
  exact Nat.le_of_add_le_add_right hTotal

/-- overlap offsetは左seed word内にある。 -/
theorem overlapOffset_le_left
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (h : R.SourceIntervalsOverlap j k) :
    R.overlapOffset j k ≤ R.length j := by
  have hs := R.overlapOffset_add_length_le_left hStart h
  omega

/-- 共通wordは右seed wordのprefixそのもの。 -/
theorem overlapWord_eq_right_take
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (h : R.SourceIntervalsOverlap j k) :
    R.overlapWord j k =
      (R.word k).take (R.overlapLength j k) := by
  have hle := R.overlapLength_le_right h
  unfold overlapWord word
  symm
  exact O.segmentWord_take_of_le hle

/-- 共通wordは左seed wordをoffsetだけdropした後のprefixでもある。 -/
theorem overlapWord_eq_left_drop_take
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (h : R.SourceIntervalsOverlap j k) :
    R.overlapWord j k =
      ((R.word j).drop (R.overlapOffset j k)).take
        (R.overlapLength j k) := by
  have hOffset := R.overlapOffset_le_left hStart h
  have hCombined := R.overlapOffset_add_length_le_left hStart h
  have hRemain :
      R.overlapLength j k ≤ R.length j - R.overlapOffset j k := by
    omega
  have hStartEq := R.start_add_overlapOffset hStart
  unfold word overlapWord
  rw [O.segmentWord_drop_of_le hOffset]
  rw [hStartEq]
  symm
  exact O.segmentWord_take_of_le hRemain

/-- overlap共通wordはactual orbit上の本物の有限run。 -/
theorem overlapWord_runs
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    Runs
      (R.overlapWord j k)
      (O.value (R.start k))
      (O.value (R.start k + R.overlapLength j k)) := by
  unfold overlapWord
  exact O.runs_segment (R.start k) (R.overlapLength j k)

/-- overlap共通wordはactual affine realizationも満たす。 -/
theorem overlapWord_realizes
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    Realizes
      (R.overlapWord j k)
      (O.value (R.start k))
      (O.value (R.start k + R.overlapLength j k)) :=
  (R.overlapWord_runs j k).realizes

/-- overlap共通wordのodd step数は共通部分長に一致する。 -/
theorem overlapWord_oddSteps
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    oddSteps (R.overlapWord j k) = R.overlapLength j k := by
  simp [overlapWord, oddSteps]

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
