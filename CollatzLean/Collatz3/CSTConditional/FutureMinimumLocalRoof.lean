import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeight
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: future minimum から見た局所 Beatty roof defect

Global CST の下では、future minimum を始点とする任意の finite segment は
coefficient-contracting 側へ入れない。既存 `segmentBeattyExcess` は

`twoSteps(segment) - beattyIndex(length)`

なので、その値が `0` であることから actual segment depth は Beatty roof 以下にある。

このファイルでは、その「roof から何段下か」だけを

`futureMinimum_localRoofDefect O i r
  = beattyIndex r - twoSteps (segmentWord i r)`

という一つの自然数座標として追加する。
新しい orbit packet / profile structure / Ferrers state は導入しない。

そこから derived theorem として

* next future minimum block の total depth は exact に `beattyIndex(length)`、
* 任意 future-minimum prefix では
  `twoSteps + localRoofDefect = beattyIndex`、
* global normalized escape increment を開始 future minimum の scale へ戻すと
  `criticalEscapeWeight / 2^localRoofDefect`

を得る。

最後の式が、A 型の real escape tail と RecordFerrers/Beatty roof の局所深さを
同じ重みで比較するための基本 exact bridge である。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
future minimum を始点とする local segment が、同じ長さの Beatty roof から何段下にあるか。

定義自体には future-minimum 仮定を埋め込まない。
実際に通常の差として使えることは Global CST + `FutureMinimumAt` から derived theorem で示す。
-/
def futureMinimum_localRoofDefect
    (O : Collatz3.OddOrbit)
    (start length : ℕ) : ℕ :=
  Critical.beattyIndex length -
    Word.twoSteps (O.segmentWord start length)

/--
Global CST 下では next future minimum block の total two-depth は
同じ長さの Beatty roof に exact に一致する。

既存の

* next future minimum なら `beattyIndex(length) ≤ twoSteps`、
* future minimum 始点なら `segmentBeattyExcess = 0`

を直接合成した薄い wrapper。
-/
theorem nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    Word.twoSteps (O.segmentWord i (j - i)) =
      Critical.beattyIndex (j - i) := by
  have hRoof := O.nextFutureMinimum_beattyIndex_le_segmentTwoSteps hNext
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  exact
    (O.segmentBeattyExcess_eq_zero_iff_twoSteps_eq_beattyIndex
      i (j - i) hRoof).1 hZero

/--
Global CST 下では future minimum を始点とする任意の finite segment の two-depth は
同じ長さの Beatty roof 以下。

`segmentBeattyExcess = twoSteps - beattyIndex = 0` の Nat.sub の意味を
明示的な大小関係へ戻したもの。
-/
theorem segmentTwoSteps_le_beattyIndex_of_futureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    Word.twoSteps (O.segmentWord start length) ≤
      Critical.beattyIndex length := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := length) G hStart
  unfold segmentBeattyExcess at hZero
  omega

/--
future minimum local roof defect は、Global CST 下では通常の整数差として exact に働く。

`twoSteps(segment) + localRoofDefect = beattyIndex(length)`。
-/
theorem segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    Word.twoSteps (O.segmentWord start length) +
        O.futureMinimum_localRoofDefect start length =
      Critical.beattyIndex length := by
  have hLe :=
    O.segmentTwoSteps_le_beattyIndex_of_futureMinimum_of_globalCST
      G hStart length
  unfold futureMinimum_localRoofDefect
  omega

/--
Global CST 下の future minimum prefix では、local roof defect が `0` であることと
actual segment depth が Beatty roof に接していることは exact に同値。
-/
theorem futureMinimum_localRoofDefect_eq_zero_iff_segmentTwoSteps_eq_beattyIndex
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    O.futureMinimum_localRoofDefect start length = 0 ↔
      Word.twoSteps (O.segmentWord start length) =
        Critical.beattyIndex length := by
  have hLe :=
    O.segmentTwoSteps_le_beattyIndex_of_futureMinimum_of_globalCST
      G hStart length
  unfold futureMinimum_localRoofDefect
  omega

/--
future-minimum local roof defect で減衰させた critical escape weight。

`c_i(r) = w_r / 2^(d_i(r))`。

これは追加する二つ目の scalar coordinate であり、profile や Ferrers shape 自体は保持しない。
-/
noncomputable def futureMinimumLocalRoofContribution
    (O : Collatz3.OddOrbit)
    (start length : ℕ) : ℝ :=
  criticalEscapeWeight length /
    (2 : ℝ) ^ O.futureMinimum_localRoofDefect start length

/-- local roof contribution は常に正。 -/
theorem futureMinimumLocalRoofContribution_pos
    (O : Collatz3.OddOrbit)
    (start length : ℕ) :
    0 < O.futureMinimumLocalRoofContribution start length := by
  unfold futureMinimumLocalRoofContribution
  exact div_pos (criticalEscapeWeight_pos length) (by positivity)

/-- local roof contribution は常に非負。 -/
theorem futureMinimumLocalRoofContribution_nonneg
    (O : Collatz3.OddOrbit)
    (start length : ℕ) :
    0 ≤ O.futureMinimumLocalRoofContribution start length :=
  (O.futureMinimumLocalRoofContribution_pos start length).le

/--
Global normalized escape increment を開始 future minimum の prefix scale へ戻すと、
local roof contribution に exact に一致する。

`D_i = infinitePrefixDepth exponent i` とすると

`(3^i / 2^D_i) * (R_(i+r+1)-R_(i+r))
   = w_r / 2^(d_i(r))`。

global index `i+r` の Beatty phase を直接 local row `r` と同一視せず、
actual prefix depth の exact additivity を介して scale を移すのが重要。
-/
theorem scaledEscapeIncrement_eq_criticalEscapeWeight_div_localRoofDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    ((3 : ℝ) ^ start /
          (2 : ℝ) ^ infinitePrefixDepth O.exponent start) *
        O.normalizedEscapeIncrement (start + length) =
      O.futureMinimumLocalRoofContribution start length := by
  have hRoof :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hStart length
  unfold futureMinimumLocalRoofContribution
  unfold normalizedEscapeIncrement
  unfold criticalEscapeWeight
  rw [O.infinitePrefixDepth_add_eq start length]
  rw [← hRoof]
  rw [show start + length + 1 = start + (length + 1) by omega]
  simp only [pow_add]
  field_simp

end OddOrbit
end Collatz3
