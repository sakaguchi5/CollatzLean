import CollatzLean.Collatz3.Bridge.SurvivorSegmentDefect

/-!
# Collatz3 Bridge: 隣接 future minimum block の defect 算術

`NextFutureMinimum i j` を一つだけ取り、旧 AdjacentReturn の大きな State 構造を復活させずに、
actual segment `[i,j]` の情報を現行 `Collatz3` の正本へ戻す。

中心は次の二点。

1. whole block は Beatty roof 以上の two-depth を持つ。
2. proper suffix は actual 値として strict に下がるので、Beatty roof を少なくとも 1 段越える。

これを `segmentBeattyExcess` と `beattyCarry` の保存則へ入れると、whole block では

`δ_j + q = δ_i + c`,  `c ∈ {0,1}`

となる。従って defect は一つの next future minimum へ進むとき高々 1 しか増えず、
`+1` が起きるのは `carry = 1` かつ `q = 0` の場合に限る。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/-- infinite coefficient survivor の actual 値はどの時刻でも `1` より大きい。 -/
theorem one_lt_value_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (n : ℕ) :
    1 < O.value n := by
  have hOneLe := O.one_le_value n
  have hNe : O.value n ≠ 1 := by
    intro hOne
    apply O.no_hitsOne_of_infiniteCoefficientSurvivor S
    exact ⟨n, hOne⟩
  omega

/-- survivor 軌道の future minimum では exponent が exact に `1`。 -/
theorem futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {n : ℕ}
    (hMin : O.FutureMinimumAt n) :
    O.exponent n = 1 := by
  exact
    FutureMinimumAt.exponent_eq_one_of_one_lt
      hMin
      (O.one_lt_value_of_infiniteCoefficientSurvivor S n)

/-- survivor 軌道の next future minimum endpoint では exponent が exact に `1`。 -/
theorem nextFutureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    O.exponent j = 1 := by
  exact O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hNext.futureMinimumAt

/--
next future minimum までの whole segment は、同じ長さの Beatty roof 以上の two-depth を持つ。

`j` は `i+1` よりも値が小さく、一般 segment 補題へそのまま落ちる。
-/
theorem nextFutureMinimum_beattyIndex_le_segmentTwoSteps
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    Critical.beattyIndex (j - i) ≤
      Word.twoSteps (O.segmentWord i (j - i)) := by
  have hLength : 0 < j - i := Nat.sub_pos_of_lt hNext.1
  have hIndex : i + (j - i) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hEnd :
      O.value (i + (j - i)) ≤ O.value (i + 1) := by
    rw [hIndex]
    exact hNext.2 (i + 1) (by omega)
  exact O.beattyIndex_le_segmentTwoSteps_of_end_le_next hLength hEnd

/--
next future minimum whole block の actual depth を `Beatty roof + excess` に exact 分解する。
-/
theorem nextFutureMinimum_beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    Critical.beattyIndex (j - i) + O.segmentBeattyExcess i (j - i) =
      Word.twoSteps (O.segmentWord i (j - i)) := by
  exact
    O.beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
      i (j - i)
      (O.nextFutureMinimum_beattyIndex_le_segmentTwoSteps hNext)

/--
next future minimum block に対する exact defect 保存則。

`q = segmentBeattyExcess`, `c = beattyCarry` と書けば
`δ_j + q = δ_i + c`。
-/
theorem nextFutureMinimum_defect_balance
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j +
        O.segmentBeattyExcess i (j - i) =
      infiniteSurvivorDefect O.exponent i +
        Critical.beattyCarry i (j - i) := by
  have hRoof := O.nextFutureMinimum_beattyIndex_le_segmentTwoSteps hNext
  have hBalance :=
    O.segmentDefect_add_segmentBeattyExcess_eq S i (j - i) hRoof
  have hIndex : i + (j - i) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  rw [hIndex] at hBalance
  exact hBalance

/-- next future minimum へ進む一回の transition で defect は高々 1 しか増えない。 -/
theorem nextFutureMinimum_defect_le_add_one
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j ≤
      infiniteSurvivorDefect O.exponent i + 1 := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  have hCarry := Critical.beattyCarry_le_one i (j - i)
  omega

/-- carry が 0 の next future minimum block では defect は増えない。 -/
theorem nextFutureMinimum_defect_le_of_carry_eq_zero
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hCarry : Critical.beattyCarry i (j - i) = 0) :
    infiniteSurvivorDefect O.exponent j ≤
      infiniteSurvivorDefect O.exponent i := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  omega

/--
next future minimum block で defect が exact に `+1` される条件。

`+1` は `carry = 1` かつ segment excess `q = 0` の場合に限り、逆も成り立つ。
-/
theorem nextFutureMinimum_defect_eq_succ_iff
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 ↔
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 0 := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  have hCarry := Critical.beattyCarry_le_one i (j - i)
  constructor
  · intro hSucc
    constructor <;> omega
  · rintro ⟨hCarryOne, hExcessZero⟩
    omega

/--
next future minimum block では `q=0` と coefficient-expanding が exact に同値。

ここで expanding は新しい predicate を作らず、power inequality
`2^H < 3^L` をそのまま正本として使う。
-/
theorem nextFutureMinimum_segmentBeattyExcess_eq_zero_iff_twoPow_lt_threePow
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    O.segmentBeattyExcess i (j - i) = 0 ↔
      2 ^ Word.twoSteps (O.segmentWord i (j - i)) < 3 ^ (j - i) := by
  have hLength : 0 < j - i := Nat.sub_pos_of_lt hNext.1
  have hRoof := O.nextFutureMinimum_beattyIndex_le_segmentTwoSteps hNext
  constructor
  · intro hZero
    exact
      O.twoPow_segment_lt_threePow_of_segmentBeattyExcess_eq_zero
        hLength hRoof hZero
  · intro hExpanding
    have hDepthLe :=
      Critical.le_beattyIndex_of_twoPow_lt_threePow hExpanding
    unfold segmentBeattyExcess
    omega

/--
next future minimum block では positive excess と strict contracting が exact に同値。
-/
theorem nextFutureMinimum_segmentBeattyExcess_pos_iff_threePow_lt_twoPow
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    0 < O.segmentBeattyExcess i (j - i) ↔
      3 ^ (j - i) < 2 ^ Word.twoSteps (O.segmentWord i (j - i)) := by
  constructor
  · intro hPos
    exact O.threePow_lt_twoPow_segment_of_segmentBeattyExcess_pos hPos
  · intro hContracting
    by_contra hNot
    have hZero : O.segmentBeattyExcess i (j - i) = 0 := by omega
    have hExpanding :=
      (O.nextFutureMinimum_segmentBeattyExcess_eq_zero_iff_twoPow_lt_threePow hNext).1
        hZero
    omega

/-- contracting next future minimum block では defect は増えない。 -/
theorem nextFutureMinimum_defect_le_of_threePow_lt_twoPow
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hContracting :
      3 ^ (j - i) < 2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    infiniteSurvivorDefect O.exponent j ≤
      infiniteSurvivorDefect O.exponent i := by
  have hPos :=
    (O.nextFutureMinimum_segmentBeattyExcess_pos_iff_threePow_lt_twoPow hNext).2
      hContracting
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  have hCarry := Critical.beattyCarry_le_one i (j - i)
  omega

/--
`defect +1` を power inequality で読み直した形。

隣接 transition で defect が増える唯一の型は
`carry = 1` かつ whole block が strict expanding である。
-/
theorem nextFutureMinimum_defect_eq_succ_iff_carry_one_and_expanding
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 ↔
      Critical.beattyCarry i (j - i) = 1 ∧
        2 ^ Word.twoSteps (O.segmentWord i (j - i)) < 3 ^ (j - i) := by
  constructor
  · intro hSucc
    rcases (O.nextFutureMinimum_defect_eq_succ_iff S hNext).1 hSucc with
      ⟨hCarry, hZero⟩
    exact
      ⟨hCarry,
        (O.nextFutureMinimum_segmentBeattyExcess_eq_zero_iff_twoPow_lt_threePow hNext).1
          hZero⟩
  · rintro ⟨hCarry, hExpanding⟩
    apply (O.nextFutureMinimum_defect_eq_succ_iff S hNext).2
    exact
      ⟨hCarry,
        (O.nextFutureMinimum_segmentBeattyExcess_eq_zero_iff_twoPow_lt_threePow hNext).2
          hExpanding⟩

/--
next future minimum block で defect が減らない場合、`(carry, excess)` は三型しかない。

* `(0,0)` : defect 不変、expanding
* `(1,0)` : defect `+1`、expanding
* `(1,1)` : defect 不変、最小 contracting

これは新しい分類 structure を作らず、三つの conjunction の disjunction として保存する。
-/
theorem nextFutureMinimum_nondec_three_cases
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hNondec :
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent j) :
    (Critical.beattyCarry i (j - i) = 0 ∧
        O.segmentBeattyExcess i (j - i) = 0 ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i) ∨
      (Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 0 ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i + 1) ∨
      (Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1 ∧
        infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i) := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  rcases Critical.beattyCarry_eq_zero_or_one i (j - i) with hCarry | hCarry
  · left
    constructor
    · exact hCarry
    constructor <;> omega
  · by_cases hExcess : O.segmentBeattyExcess i (j - i) = 0
    · right
      left
      exact ⟨hCarry, hExcess, by omega⟩
    · right
      right
      have hExcessPos : 0 < O.segmentBeattyExcess i (j - i) := by omega
      exact ⟨hCarry, by omega, by omega⟩

/-- excess が 2 以上なら、next future minimum transition で defect は少なくとも 1 下がる。 -/
theorem nextFutureMinimum_defect_add_one_le_of_two_le_segmentBeattyExcess
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hExcess : 2 ≤ O.segmentBeattyExcess i (j - i)) :
    infiniteSurvivorDefect O.exponent j + 1 ≤
      infiniteSurvivorDefect O.exponent i := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  have hCarry := Critical.beattyCarry_le_one i (j - i)
  omega

/-- excess 1 かつ carry 1 は、defect が不変な最小 contracting transition。 -/
theorem nextFutureMinimum_defect_eq_of_carry_one_excess_one
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hCarry : Critical.beattyCarry i (j - i) = 1)
    (hExcess : O.segmentBeattyExcess i (j - i) = 1) :
    infiniteSurvivorDefect O.exponent j =
      infiniteSurvivorDefect O.exponent i := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  omega

/-- excess 0 かつ carry 0 は、defect が不変な expanding transition。 -/
theorem nextFutureMinimum_defect_eq_of_carry_zero_excess_zero
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hCarry : Critical.beattyCarry i (j - i) = 0)
    (hExcess : O.segmentBeattyExcess i (j - i) = 0) :
    infiniteSurvivorDefect O.exponent j =
      infiniteSurvivorDefect O.exponent i := by
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  omega

/--
next future minimum の真の内部位置では、終点値は internal value より strict に小さい。

`NextFutureMinimum` から weak inequality を得て、等号は nontrivial repeat になるため
infinite coefficient survivor では除外される。
-/
theorem nextFutureMinimum_value_lt_internal
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    O.value j < O.value k := by
  have hLe : O.value j ≤ O.value k := hNext.2 k hik
  have hKNeOne : O.value k ≠ 1 := by
    intro hOne
    apply O.no_hitsOne_of_infiniteCoefficientSurvivor S
    exact ⟨k, hOne⟩
  have hNe : O.value k ≠ O.value j := by
    intro hEq
    apply O.no_nontrivialRepeat_of_infiniteCoefficientSurvivor S
    exact ⟨k, j, hkj, hEq, hKNeOne⟩
  omega

/-- next future minimum の任意 proper suffix は coefficient として strict contracting。 -/
theorem nextFutureMinimum_properSuffix_threePow_lt_twoPow
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    3 ^ (j - k) < 2 ^ Word.twoSteps (O.segmentWord k (j - k)) := by
  have hLength : 0 < j - k := Nat.sub_pos_of_lt hkj
  have hIndex : k + (j - k) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hkj)
  have hDec : O.value (k + (j - k)) < O.value k := by
    rw [hIndex]
    exact O.nextFutureMinimum_value_lt_internal S hNext hik hkj
  exact O.threePow_lt_twoPow_segment_of_end_lt_start hLength hDec

/--
next future minimum の任意 proper suffix は strict contracting であり、
その two-depth は `criticalTwoDepth` 以上。
-/
theorem nextFutureMinimum_properSuffix_criticalTwoDepth_le
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    Critical.criticalTwoDepth (j - k) ≤
      Word.twoSteps (O.segmentWord k (j - k)) := by
  have hLength : 0 < j - k := Nat.sub_pos_of_lt hkj
  have hIndex : k + (j - k) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hkj)
  have hDec : O.value (k + (j - k)) < O.value k := by
    rw [hIndex]
    exact O.nextFutureMinimum_value_lt_internal S hNext hik hkj
  exact
    O.criticalTwoDepth_le_segmentTwoSteps_of_end_lt_start hLength hDec

/-- proper suffix の Beatty excess は少なくとも 1。 -/
theorem nextFutureMinimum_properSuffix_segmentBeattyExcess_pos
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    0 < O.segmentBeattyExcess k (j - k) := by
  have hCritical :=
    O.nextFutureMinimum_properSuffix_criticalTwoDepth_le S hNext hik hkj
  unfold segmentBeattyExcess
  unfold Critical.criticalTwoDepth at hCritical
  omega
/--
proper suffix に対する exact defect 保存則。

whole block と同じ式
`δ_j + q_suffix = δ_k + carry(k,j-k)`
が成立し、さらに proper suffix では `q_suffix≥1` が別定理で保証される。
-/
theorem nextFutureMinimum_properSuffix_defect_balance
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    infiniteSurvivorDefect O.exponent j +
        O.segmentBeattyExcess k (j - k) =
      infiniteSurvivorDefect O.exponent k +
        Critical.beattyCarry k (j - k) := by
  have hCritical :=
    O.nextFutureMinimum_properSuffix_criticalTwoDepth_le S hNext hik hkj
  have hRoof :
      Critical.beattyIndex (j - k) ≤
        Word.twoSteps (O.segmentWord k (j - k)) := by
    unfold Critical.criticalTwoDepth at hCritical
    omega
  have hBalance :=
    O.segmentDefect_add_segmentBeattyExcess_eq S k (j - k) hRoof
  have hIndex : k + (j - k) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hkj)
  rw [hIndex] at hBalance
  exact hBalance

/--
next future minimum の任意 proper internal point から終点へ進むと defect は増えない。

proper suffix は `q≥1`、Beatty carry は高々 `1` なので、保存則
`δ_j + q = δ_k + c` から従う。
-/
theorem nextFutureMinimum_defect_le_internal
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j) :
    infiniteSurvivorDefect O.exponent j ≤
      infiniteSurvivorDefect O.exponent k := by
  have hBalance :=
    O.nextFutureMinimum_properSuffix_defect_balance S hNext hik hkj
  have hPos :=
    O.nextFutureMinimum_properSuffix_segmentBeattyExcess_pos S hNext hik hkj
  have hCarry := Critical.beattyCarry_le_one k (j - k)
  omega

/--
proper suffix の carry が 0 なら defect は少なくとも 1 下がる。
-/
theorem nextFutureMinimum_defect_add_one_le_internal_of_carry_eq_zero
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hik : i < k)
    (hkj : k < j)
    (hCarry : Critical.beattyCarry k (j - k) = 0) :
    infiniteSurvivorDefect O.exponent j + 1 ≤
      infiniteSurvivorDefect O.exponent k := by
  have hBalance :=
    O.nextFutureMinimum_properSuffix_defect_balance S hNext hik hkj
  have hPos :=
    O.nextFutureMinimum_properSuffix_segmentBeattyExcess_pos S hNext hik hkj
  omega

end OddOrbit
end Collatz3
