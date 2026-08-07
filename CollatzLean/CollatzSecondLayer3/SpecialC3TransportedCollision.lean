import CollatzLean.CollatzSecondLayer3.SpecialC3AlignmentPropagation
import CollatzLean.CollatzFirstLayer.CommonWordDifference

/-!
# overlap内で輸送したnegative centerとexact collision排除

左側Special C3 seedのnegative predecessor centerを、右側seed startまで
actual prefixと同じ指数語で整数輸送する。
輸送後の値は

`actual value - 3^offset * 2^(tailTwoSteps+1)`

とexactに書ける。
これが右seed自身のnegative center

`actual value - 2^(rightTwoSteps+1)`

と一致すると、正のoffsetに対して3冪を含む数と純粋な2冪が等しくなり矛盾する。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- 左seed startから右seed startまでのactual prefix word。 -/
def leftPrefixWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ExpWord :=
  O.segmentWord (R.start j) (R.overlapOffset j k)

/-- 右seed startから左seed endまでの残り長。 -/
def leftTailLength
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℕ :=
  R.length j - R.overlapOffset j k

/-- 右seed startから左seed endまでのactual tail word。 -/
def leftTailWord
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ExpWord :=
  O.segmentWord (R.start k) (R.leftTailLength j k)

/-- overlap順序の下で左seed wordをprefixとtailへ分解する。 -/
theorem word_eq_leftPrefix_append_leftTail
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (hOverlap : R.SourceIntervalsOverlap j k) :
    R.word j = R.leftPrefixWord j k ++ R.leftTailWord j k := by
  have hOffset := R.overlapOffset_le_left hStart hOverlap
  have hLen :
      R.length j =
        R.overlapOffset j k + R.leftTailLength j k := by
    unfold leftTailLength
    omega
  have hStartEq := R.start_add_overlapOffset hStart
  unfold word leftPrefixWord leftTailWord
  rw [hLen]
  rw [O.segmentWord_add]
  rw [hStartEq]

/-- 左seed wordの総2進depthはprefixとtailの和。 -/
theorem word_twoSteps_eq_leftPrefix_add_leftTail
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (hOverlap : R.SourceIntervalsOverlap j k) :
    twoSteps (R.word j) =
      twoSteps (R.leftPrefixWord j k) +
        twoSteps (R.leftTailWord j k) := by
  rw [R.word_eq_leftPrefix_append_leftTail hStart hOverlap]
  rw [twoSteps_append]

/-- Special C3 seedのnegative centerをactual開始値から直接書く。 -/
theorem center_eq_actual_sub_twoPow
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j : ℕ) :
    R.center j =
      (O.value (R.start j) : ℤ) -
        (2 : ℤ) ^ (twoSteps (R.word j) + 1) := by
  have hs :
      O.value (R.start j) = canonicalStart (R.word j) := by
    simpa [word, start, length, terminalTime] using
      (R.special j).canonicalStart_eq
  unfold center predecessorStart residueModulus
  rw [hs]
  push_cast
  rfl

/--
左seedのnegative centerを右seed startまでactual prefixで整数輸送した候補値。
-/
def transportedCenterFromLeft
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : ℤ :=
  (O.value (R.start k) : ℤ) -
    (3 : ℤ) ^ (R.overlapOffset j k) *
      (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1)

/--
transported centerは左prefix wordの整数actual realizationを満たす。
-/
theorem transportedCenterFromLeft_realizesInt
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j ≤ R.start k)
    (hOverlap : R.SourceIntervalsOverlap j k) :
    RealizesInt
      (R.leftPrefixWord j k)
      (R.center j)
      (R.transportedCenterFromLeft j k) := by
  have hStartEq := R.start_add_overlapOffset hStart
  have hActual0 :=
    (O.realizes_segment
      (R.start j)
      (R.overlapOffset j k)).toInt
  unfold RealizesInt at hActual0
  have hActual :
      (2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
          (O.value (R.start k) : ℤ) =
        (3 : ℤ) ^ (R.overlapOffset j k) *
          (O.value (R.start j) : ℤ) +
        affineConstInt (R.leftPrefixWord j k) := by
    simpa [leftPrefixWord, oddSteps, hStartEq] using hActual0
  have hCenter := R.center_eq_actual_sub_twoPow j
  have hSplit := R.word_twoSteps_eq_leftPrefix_add_leftTail hStart hOverlap
  have hOdd :
      oddSteps (R.leftPrefixWord j k) = R.overlapOffset j k := by
    simp [leftPrefixWord, oddSteps]
  unfold RealizesInt transportedCenterFromLeft
  rw [hCenter, hSplit, hOdd]
  have hPow :
      (2 : ℤ) ^
          (twoSteps (R.leftPrefixWord j k) +
            twoSteps (R.leftTailWord j k) + 1) =
        (2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
          (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1) := by
    rw [show
      twoSteps (R.leftPrefixWord j k) +
          twoSteps (R.leftTailWord j k) + 1 =
        twoSteps (R.leftPrefixWord j k) +
          (twoSteps (R.leftTailWord j k) + 1) by omega]
    rw [pow_add]
  rw [hPow]
  calc
    (2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
          ((O.value (R.start k) : ℤ) -
            (3 : ℤ) ^ R.overlapOffset j k *
              (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1))
        =
      (2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
          (O.value (R.start k) : ℤ) -
        (3 : ℤ) ^ R.overlapOffset j k *
          ((2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
            (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1)) := by ring
    _ =
      ((3 : ℤ) ^ R.overlapOffset j k *
          (O.value (R.start j) : ℤ) +
        affineConstInt (R.leftPrefixWord j k)) -
        (3 : ℤ) ^ R.overlapOffset j k *
          ((2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
            (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1)) := by
          rw [hActual]
    _ =
      (3 : ℤ) ^ R.overlapOffset j k *
          ((O.value (R.start j) : ℤ) -
            ((2 : ℤ) ^ twoSteps (R.leftPrefixWord j k) *
              (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1))) +
        affineConstInt (R.leftPrefixWord j k) := by ring

/-- 3の冪は奇数。 -/
private theorem odd_three_pow_nat (n : ℕ) : Odd (3 ^ n) := by
  induction n with
  | zero => exact ⟨0, by norm_num⟩
  | succ n ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨3 * u + 1, ?_⟩
      rw [pow_succ, hu]
      ring

/-- 正の3冪を含む数は純粋な2冪と等しくならない。 -/
private theorem threePow_mul_twoPow_ne_twoPow
    {d a b : ℕ}
    (hd : 0 < d) :
    3 ^ d * 2 ^ a ≠ 2 ^ b := by
  intro hEq
  have hLeft : ExactTwoFactor (2 ^ b) a (3 ^ d) := by
    refine ⟨?_, odd_three_pow_nat d⟩
    calc
      2 ^ b = 3 ^ d * 2 ^ a := hEq.symm
      _ = 2 ^ a * 3 ^ d := by ring
  have hRight : ExactTwoFactor (2 ^ b) b 1 := by
    exact ⟨by simp, ⟨0, by norm_num⟩⟩
  have hOddPart := (exactTwoFactor_unique hLeft hRight).2
  obtain ⟨r, hr⟩ : ∃ r : ℕ, d = r + 1 :=
    ⟨d - 1, by omega⟩
  rw [hr, pow_succ] at hOddPart
  have hOne : 1 ≤ 3 ^ r := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.pow_pos (by omega)))
  omega

/--
異なるstartを持つoverlap seedでは、左negative centerを右startへ輸送した値と
右seed自身のnegative centerはexactには一致できない。
-/
theorem transportedCenterFromLeft_ne_rightCenter
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (hStart : R.start j < R.start k)
    (_hOverlap : R.SourceIntervalsOverlap j k) :
    R.transportedCenterFromLeft j k ≠ R.center k := by
  intro hCollision
  have hOffsetPos : 0 < R.overlapOffset j k := by
    unfold overlapOffset
    omega
  have hCenterK := R.center_eq_actual_sub_twoPow k
  unfold transportedCenterFromLeft at hCollision
  rw [hCenterK] at hCollision
  have hShiftZ :
      (3 : ℤ) ^ R.overlapOffset j k *
          (2 : ℤ) ^ (twoSteps (R.leftTailWord j k) + 1) =
        (2 : ℤ) ^ (twoSteps (R.word k) + 1) := by
    omega
  have hShiftN :
      3 ^ R.overlapOffset j k *
          2 ^ (twoSteps (R.leftTailWord j k) + 1) =
        2 ^ (twoSteps (R.word k) + 1) := by
    exact_mod_cast hShiftZ
  exact
    (threePow_mul_twoPow_ne_twoPow hOffsetPos) hShiftN

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
