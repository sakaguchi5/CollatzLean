import CollatzLean.Collatz3.Critical.BeattyCarry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 2・3 冪で定まる臨界指数の整数算術

この層では actual orbit や Global CST を使わない。
既存の `Critical.beattyIndex` を唯一の正本として再利用し、

`2^b < 3^m < 2^(b+1)`

という power-form の整数算術だけを derived theorem としてまとめる。

新しい Beatty index は定義しない。
-/

namespace Collatz3
namespace IntegerReduction

open Critical

/-- `beattyIndex 1 = 1`。 -/
@[simp] theorem beattyIndex_one :
    Critical.beattyIndex 1 = 1 := by
  have hPos : 0 < Critical.beattyIndex 1 := by
    have h := Critical.beattyIndex_lt_succ 0
    simpa using h
  have hLe : Critical.beattyIndex 1 ≤ 1 := by
    apply Critical.beattyIndex_le_of_upper
    norm_num
  omega

/--
正の幅では `beattyIndex` は 2 と 3 の冪の間を strict に挟む。

`2^b < 3^m < 2^(b+1)`。
-/
theorem beattyIndex_power_characterization
    {m : ℕ}
    (hm : 0 < m) :
    2 ^ Critical.beattyIndex m < 3 ^ m ∧
      3 ^ m < 2 ^ (Critical.beattyIndex m + 1) := by
  constructor
  · exact Critical.beattyIndex_lower_strict hm
  · simpa [Critical.criticalTwoDepth] using
      Critical.threePow_lt_twoPow_criticalTwoDepth m

/--
`beattyIndex` は一歩ごとに exactly `+1` または `+2`。
-/
theorem beattyIndex_step_eq_add_one_or_two
    (m : ℕ) :
    Critical.beattyIndex (m + 1) = Critical.beattyIndex m + 1 ∨
      Critical.beattyIndex (m + 1) = Critical.beattyIndex m + 2 := by
  have hLower := Critical.beattyIndex_lt_succ m
  have hUpper := Critical.beattyIndex_add_upper m 1
  rw [beattyIndex_one] at hUpper
  omega

/-- `m ≤ beattyIndex m`。一歩の増分が少なくとも 1 であることの有限帰納版。 -/
theorem nat_le_beattyIndex
    (m : ℕ) :
    m ≤ Critical.beattyIndex m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hStep := Critical.beattyIndex_lt_succ m
      omega

/--
距離 `d` だけ進めば Beatty index も少なくとも `d` 増える。
-/
theorem beattyIndex_add_distance_lower
    (a d : ℕ) :
    Critical.beattyIndex a + d ≤ Critical.beattyIndex (a + d) := by
  have hd := nat_le_beattyIndex d
  have hAdd := Critical.beattyIndex_add_lower a d
  omega

/-- Beatty additive gap は `0` または `1`。 -/
theorem beattyIndex_add_gap_eq_zero_or_one
    (a b : ℕ) :
    Critical.beattyIndex (a + b) -
        (Critical.beattyIndex a + Critical.beattyIndex b) = 0 ∨
      Critical.beattyIndex (a + b) -
        (Critical.beattyIndex a + Critical.beattyIndex b) = 1 := by
  simpa [Critical.beattyCarry] using
    Critical.beattyCarry_eq_zero_or_one a b

/--
幅 `r>0` の最後の Beatty jump が `+2` なら

`2 * 3^r ≤ 3 * 2^beattyIndex(r)`。

これは後続の 3-window / 5-window counting の純整数入力になる。
-/
theorem two_mul_threePow_le_three_mul_twoPow_of_finalJumpTwo
    {r : ℕ}
    (hr : 0 < r)
    (hJump :
      Critical.beattyIndex r =
        Critical.beattyIndex (r - 1) + 2) :
    2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r := by
  have hrEq : r = (r - 1) + 1 := by
    omega
  have hPrev := Critical.beattyIndex_upper (r - 1)
  have hPrev' :
      3 ^ (r - 1) ≤
        2 ^ Critical.beattyIndex (r - 1) * 2 := by
    simpa [pow_succ] using hPrev
  have hThree :
      3 ^ r = 3 ^ (r - 1) * 3 := by
    rw [hrEq, pow_succ]
    simp
  have hTwo :
      2 ^ Critical.beattyIndex r =
        2 ^ Critical.beattyIndex (r - 1) * 4 := by
    rw [hJump, pow_add]
    norm_num
  rw [hThree, hTwo]
  nlinarith

end IntegerReduction
end Collatz3
