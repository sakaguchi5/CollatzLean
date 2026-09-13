import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RankDropArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: critical margin

critical terminal depth と連続 slope の差

`μ(m) = criticalTwoDepth(m) - m * log₂ 3`

を一つの実数関数として切り出す。

この量には二つの読み方がある。

* rotation 側では `1 - fract(m * log₂(3/2))` という terminal non-wrap margin。
* rank-drop 側では `rankDrop(m,r) = m μ(r) - r μ(m)` を与える determinant 座標。

新しい combinatorial data は導入せず、既存の power-form Beatty depth と
実数対数 bridge からすべて derived theorem として導く。
-/

namespace Collatz3
namespace Bridge

/--
critical terminal depth と連続 slope `m log₂3` の差。
-/
noncomputable def criticalMargin (m : ℕ) : ℝ :=
  (Critical.criticalTwoDepth m : ℝ) -
    (m : ℝ) * Real.logb 2 3

/--
`criticalMargin` を Beatty index で展開しただけの基本形。
-/
theorem criticalMargin_eq_beattyIndex_add_one_sub
    (m : ℕ) :
    criticalMargin m =
      (Critical.beattyIndex m : ℝ) + 1 -
        (m : ℝ) * Real.logb 2 3 := by
  unfold criticalMargin Critical.criticalTwoDepth
  push_cast
  ring

/--
Beatty cell の整数 floor は power-form `beattyIndex` と一致する。
後続の fractional-part 公式で使う局所 bridge。
-/
theorem floor_mul_logb_two_three_eq_beattyIndex
    (m : ℕ) :
    ⌊(m : ℝ) * Real.logb 2 3⌋ =
      (Critical.beattyIndex m : ℤ) := by
  have hCell := beattyIndex_isLowerMechanical_logb_two_three m
  change
    (Critical.beattyIndex m : ℝ) ≤
        (m : ℝ) * Real.logb 2 3 ∧
      (m : ℝ) * Real.logb 2 3 <
        (Critical.beattyIndex m : ℝ) + 1 at hCell
  rw [Int.floor_eq_iff]
  simpa using hCell

/--
critical margin は `m log₂3` の fractional part の補数。
-/
theorem criticalMargin_eq_one_sub_fract_logb_two_three
    (m : ℕ) :
    criticalMargin m =
      1 - Int.fract ((m : ℝ) * Real.logb 2 3) := by
  let x : ℝ := (m : ℝ) * Real.logb 2 3
  have hFloor :
      ⌊x⌋ = (Critical.beattyIndex m : ℤ) := by
    simpa [x] using floor_mul_logb_two_three_eq_beattyIndex m
  have hDecomp :
      (Critical.beattyIndex m : ℝ) + Int.fract x = x := by
    calc
      (Critical.beattyIndex m : ℝ) + Int.fract x =
          (((⌊x⌋ : ℤ) : ℝ) + Int.fract x) := by
            rw [hFloor]
            simp
      _ = x := by
            exact Int.floor_add_fract x
  rw [criticalMargin_eq_beattyIndex_add_one_sub]
  dsimp [x] at hDecomp
  linarith

/--
`log₂(3/2) = log₂3 - 1` なので、整数 shift を fractional part から消せる。
-/
theorem fract_mul_collatzRotation_eq_fract_mul_logb_two_three
    (m : ℕ) :
    Int.fract
        ((m : ℝ) * Real.logb 2 ((3 : ℝ) / 2)) =
      Int.fract ((m : ℝ) * Real.logb 2 3) := by
  have hShift :
      (m : ℝ) * Real.logb 2 ((3 : ℝ) / 2) =
        (m : ℝ) * Real.logb 2 3 +
          (((-(m : ℤ) : ℤ)) : ℝ) := by
    rw [logb_two_three_div_two]
    push_cast
    ring
  rw [hShift, Int.fract_add_intCast]

/--
rotation 座標で読んだ terminal non-wrap margin。

`μ(m) = 1 - fract(m log₂(3/2))`。
-/
theorem criticalMargin_eq_one_sub_fract_collatzRotation
    (m : ℕ) :
    criticalMargin m =
      1 -
        Int.fract
          ((m : ℝ) * Real.logb 2 ((3 : ℝ) / 2)) := by
  rw [
    criticalMargin_eq_one_sub_fract_logb_two_three,
    fract_mul_collatzRotation_eq_fract_mul_logb_two_three
  ]

/-- critical margin は常に strict に正。 -/
theorem criticalMargin_pos
    (m : ℕ) :
    0 < criticalMargin m := by
  rw [criticalMargin_eq_one_sub_fract_logb_two_three]
  have h := Int.fract_lt_one ((m : ℝ) * Real.logb 2 3)
  linarith

/-- critical margin は `1` 以下。 -/
theorem criticalMargin_le_one
    (m : ℕ) :
    criticalMargin m ≤ 1 := by
  rw [criticalMargin_eq_one_sub_fract_logb_two_three]
  have h := Int.fract_nonneg ((m : ℝ) * Real.logb 2 3)
  linarith

/--
Beatty rank drop は二つの critical margin の determinant に exact に一致する。

`d_m(r) = m μ(r) - r μ(m)`。

連続 slope `log₂3` の項は determinant 内で完全に相殺される。
-/
theorem rankDropInt_beatty_cast_eq_marginDeterminant
    (m r : ℕ) :
    (Experimental2.GenericRecordFerrers.rankDropInt
        Critical.beattyIndex m r : ℝ) =
      (m : ℝ) * criticalMargin r -
        (r : ℝ) * criticalMargin m := by
  rw [
    Experimental2.GenericRecordFerrers.rankDropInt_eq_roofFormula
  ]
  unfold criticalMargin Critical.criticalTwoDepth
  push_cast
  ring

end Bridge
end Collatz3
