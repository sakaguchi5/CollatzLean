import CollatzLean.Collatz3.Bridge.InfiniteSurvivorEscape
import CollatzLean.Collatz3.Critical.BeattyCarry

/-!
# Collatz3 Bridge: actual segment の Beatty excess と survivor defect 保存則

`d08e66d...` 以後に得られた future-minimum 間の算術を、まず一般の actual segment に
切り出す。

新しい primitive data は導入しない。追加する定義は、segment の total two-depth が
同じ長さの Beatty roof を何段越えたかを表す `segmentBeattyExcess` だけである。

* `D_(a+r) = D_a + H`
* `B_(a+r) = B_a + B_r + carry`
* `δ_m = B_m - D_m`

から、`B_r ≤ H` の範囲では

`δ_(a+r) + (H-B_r) = δ_a + beattyCarry a r`

が exact に成り立つ。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
actual segment の total two-depth が、同じ長さの Beatty roof を何段越えたか。

future minimum 専用の structure にはせず、任意の actual segment に対する薄い座標として置く。
`B_r ≤ H` が分かっている場合には、これは通常の整数差 `H-B_r` そのものである。
-/
def segmentBeattyExcess
    (O : Collatz3.OddOrbit)
    (start length : ℕ) : ℕ :=
  Word.twoSteps (O.segmentWord start length) - Critical.beattyIndex length

/--
actual odd-only 一歩の終点は、開始値の 2 倍以下。

`2^e y' = 3y+1`, `e≥1`, `y≥1` だけから従う。
future minimum の仮定は使わない。
-/
theorem value_succ_le_two_mul
    (O : Collatz3.OddOrbit)
    (n : ℕ) :
    O.value (n + 1) ≤ 2 * O.value n := by
  have hePos := O.exponent_pos n
  have heOne : 1 ≤ O.exponent n := by omega
  have hPow : 2 ≤ 2 ^ O.exponent n := by
    have h := Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ)) heOne
    norm_num at h
    exact h
  have hStep := (O.step n).equation
  have hValueOne : 1 ≤ O.value n := by
    rcases O.value_odd n with ⟨q, hq⟩
    omega
  have hScaled :
      2 * O.value (n + 1) ≤ 4 * O.value n := by
    calc
      2 * O.value (n + 1)
          ≤ 2 ^ O.exponent n * O.value (n + 1) :=
            Nat.mul_le_mul_right (O.value (n + 1)) hPow
      _ = 3 * O.value n + 1 := hStep
      _ ≤ 4 * O.value n := by omega
  omega

/--
segment 終点が一歩後の値以下なら、その segment depth は Beatty roof 以上。

`y_(a+r) ≤ y_(a+1) ≤ 2 y_a` と actual affine equation から
`3^r < 2^(H+1)` を得て、Beatty index の最小性へ戻す。
-/
theorem beattyIndex_le_segmentTwoSteps_of_end_le_next
    (O : Collatz3.OddOrbit)
    {start length : ℕ}
    (hLength : 0 < length)
    (hEnd : O.value (start + length) ≤ O.value (start + 1)) :
    Critical.beattyIndex length ≤
      Word.twoSteps (O.segmentWord start length) := by
  let w := O.segmentWord start length
  have hNonempty : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps start length
    change Word.oddSteps w = length at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hAffinePos : 0 < Word.affineConst w :=
    Bridge.affineConst_pos_of_nonempty hNonempty
  have hRun : Runs w (O.value start) (O.value (start + length)) := by
    simpa [w] using O.runsSegment start length
  have hEq :=
    (Word.endpointEquation_iff w (O.value start) (O.value (start + length))).1
      hRun.endpointEquation
  have hStrictRaw :
      3 ^ Word.oddSteps w * O.value start <
        2 ^ Word.twoSteps w * O.value (start + length) := by
    calc
      3 ^ Word.oddSteps w * O.value start
          < 3 ^ Word.oddSteps w * O.value start + Word.affineConst w :=
            Nat.lt_add_of_pos_right hAffinePos
      _ = 2 ^ Word.twoSteps w * O.value (start + length) := hEq.symm
  have hNext : O.value (start + 1) ≤ 2 * O.value start :=
    O.value_succ_le_two_mul start
  have hEndBound : O.value (start + length) ≤ 2 * O.value start :=
    le_trans hEnd hNext
  have hScaled :
      3 ^ length * O.value start <
        2 ^ (Word.twoSteps w + 1) * O.value start := by
    calc
      3 ^ length * O.value start
          < 2 ^ Word.twoSteps w * O.value (start + length) := by
            simpa [w] using hStrictRaw
      _ ≤ 2 ^ Word.twoSteps w * (2 * O.value start) :=
            Nat.mul_le_mul_left _ hEndBound
      _ = 2 ^ (Word.twoSteps w + 1) * O.value start := by
            rw [pow_succ]
            ring
  have hStartPos : 0 < O.value start := by
    rcases O.value_odd start with ⟨q, hq⟩
    omega
  have hPower :
      3 ^ length < 2 ^ (Word.twoSteps w + 1) :=
    (Nat.mul_lt_mul_right hStartPos).mp hScaled
  have hBeatty := Critical.beattyIndex_le_of_upper (Nat.le_of_lt hPower)
  simpa [w] using hBeatty

/--
actual segment が開始値より真に小さい値で終わるなら、coefficient は strict contracting。

`3^r y_start < 2^H y_end < 2^H y_start` を actual affine equation から直接得る。
-/
theorem threePow_lt_twoPow_segment_of_end_lt_start
    (O : Collatz3.OddOrbit)
    {start length : ℕ}
    (hLength : 0 < length)
    (hEnd : O.value (start + length) < O.value start) :
    3 ^ length < 2 ^ Word.twoSteps (O.segmentWord start length) := by
  let w := O.segmentWord start length
  have hNonempty : w ≠ [] := by
    intro hw
    have hLen := O.segmentWord_oddSteps start length
    change Word.oddSteps w = length at hLen
    rw [hw] at hLen
    simp at hLen
    omega
  have hAffinePos : 0 < Word.affineConst w :=
    Bridge.affineConst_pos_of_nonempty hNonempty
  have hRun : Runs w (O.value start) (O.value (start + length)) := by
    simpa [w] using O.runsSegment start length
  have hEq :=
    (Word.endpointEquation_iff w (O.value start) (O.value (start + length))).1
      hRun.endpointEquation
  have hPowPos : 0 < 2 ^ Word.twoSteps w :=
    Nat.pow_pos (by decide)
  have hProd :
      3 ^ Word.oddSteps w * O.value start <
        2 ^ Word.twoSteps w * O.value start := by
    calc
      3 ^ Word.oddSteps w * O.value start
          < 3 ^ Word.oddSteps w * O.value start + Word.affineConst w :=
            Nat.lt_add_of_pos_right hAffinePos
      _ = 2 ^ Word.twoSteps w * O.value (start + length) := hEq.symm
      _ < 2 ^ Word.twoSteps w * O.value start :=
            (Nat.mul_lt_mul_left hPowPos).2 hEnd
  have hStartPos : 0 < O.value start := by
    rcases O.value_odd start with ⟨q, hq⟩
    omega
  have hCoeff := (Nat.mul_lt_mul_right hStartPos).mp hProd
  simpa [w] using hCoeff

/--
strict contracting actual segment は Beatty roof を少なくとも 1 段越える。
すなわち `criticalTwoDepth r = beattyIndex r + 1 ≤ H`。
-/
theorem criticalTwoDepth_le_segmentTwoSteps_of_end_lt_start
    (O : Collatz3.OddOrbit)
    {start length : ℕ}
    (hLength : 0 < length)
    (hEnd : O.value (start + length) < O.value start) :
    Critical.criticalTwoDepth length ≤
      Word.twoSteps (O.segmentWord start length) := by
  have hContract :=
    O.threePow_lt_twoPow_segment_of_end_lt_start hLength hEnd
  have hLower := Critical.beattyIndex_lower length
  by_contra hNot
  have hDepthLe :
      Word.twoSteps (O.segmentWord start length) ≤
        Critical.beattyIndex length := by
    unfold Critical.criticalTwoDepth at hNot
    omega
  have hPowLe :
      2 ^ Word.twoSteps (O.segmentWord start length) ≤
        2 ^ Critical.beattyIndex length :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepthLe
  have hContra : 3 ^ length < 3 ^ length :=
    lt_of_lt_of_le hContract (le_trans hPowLe hLower)
  exact (Nat.lt_irrefl _ hContra)

/--
`B_r ≤ H` の範囲では、Beatty roof と `segmentBeattyExcess` の和は actual depth そのもの。
`Nat.sub` の切り捨てが起きないことを明示する基本 bridge。
-/
theorem beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
    (O : Collatz3.OddOrbit)
    (start length : ℕ)
    (hRoof :
      Critical.beattyIndex length ≤
        Word.twoSteps (O.segmentWord start length)) :
    Critical.beattyIndex length + O.segmentBeattyExcess start length =
      Word.twoSteps (O.segmentWord start length) := by
  unfold segmentBeattyExcess
  omega

/-- `B_r ≤ H` の範囲では excess zero と `H=B_r` は同値。 -/
theorem segmentBeattyExcess_eq_zero_iff_twoSteps_eq_beattyIndex
    (O : Collatz3.OddOrbit)
    (start length : ℕ)
    (hRoof :
      Critical.beattyIndex length ≤
        Word.twoSteps (O.segmentWord start length)) :
    O.segmentBeattyExcess start length = 0 ↔
      Word.twoSteps (O.segmentWord start length) = Critical.beattyIndex length := by
  unfold segmentBeattyExcess
  omega

/--
segment depth が Beatty roof 以上なら、survivor defect の変化は exact に

`δ_(a+r) + excess = δ_a + carry`

である。これが future-minimum block に使う基本保存則。
-/
theorem segmentDefect_add_segmentBeattyExcess_eq
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (start length : ℕ)
    (hRoof :
      Critical.beattyIndex length ≤
        Word.twoSteps (O.segmentWord start length)) :
    infiniteSurvivorDefect O.exponent (start + length) +
        O.segmentBeattyExcess start length =
      infiniteSurvivorDefect O.exponent start +
        Critical.beattyCarry start length := by
  have hDepth := O.infinitePrefixDepth_add_eq start length
  have hBeatty := Critical.beattyIndex_add_eq start length
  have hStart := beattyIndex_eq_prefixDepth_add_defect S start
  have hEnd := beattyIndex_eq_prefixDepth_add_defect S (start + length)
  have hExcess :=
    O.beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps start length hRoof
  omega

/-- Beatty excess が 0 で depth が roof 以上なら、segment は strict expanding 側。 -/
theorem twoPow_segment_lt_threePow_of_segmentBeattyExcess_eq_zero
    (O : Collatz3.OddOrbit)
    {start length : ℕ}
    (hLength : 0 < length)
    (hRoof :
      Critical.beattyIndex length ≤
        Word.twoSteps (O.segmentWord start length))
    (hZero : O.segmentBeattyExcess start length = 0) :
    2 ^ Word.twoSteps (O.segmentWord start length) < 3 ^ length := by
  have hDepthEq :
      Word.twoSteps (O.segmentWord start length) =
        Critical.beattyIndex length := by
    unfold segmentBeattyExcess at hZero
    omega
  rw [hDepthEq]
  exact Critical.beattyIndex_lower_strict hLength

/-- Beatty excess が正なら、その segment は strict contracting 側。 -/
theorem threePow_lt_twoPow_segment_of_segmentBeattyExcess_pos
    (O : Collatz3.OddOrbit)
    {start length : ℕ}
    (hPos : 0 < O.segmentBeattyExcess start length) :
    3 ^ length < 2 ^ Word.twoSteps (O.segmentWord start length) := by
  have hDepth :
      Critical.criticalTwoDepth length ≤
        Word.twoSteps (O.segmentWord start length) := by
    unfold segmentBeattyExcess at hPos
    unfold Critical.criticalTwoDepth
    omega
  have hCritical := Critical.threePow_lt_twoPow_criticalTwoDepth length
  have hPow :
      2 ^ Critical.criticalTwoDepth length ≤
        2 ^ Word.twoSteps (O.segmentWord start length) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  exact lt_of_lt_of_le hCritical hPow

end OddOrbit
end Collatz3
