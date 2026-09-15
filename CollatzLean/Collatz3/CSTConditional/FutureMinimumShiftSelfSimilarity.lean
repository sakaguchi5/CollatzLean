import CollatzLean.Collatz3.CSTConditional.FutureMinimumDefectExact
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth

/-!
# Collatz3 CSTConditional: future-minimum shift と A 型の局所自己相似性

future minimum `start` から軌道を見直すため、`OddOrbit` の単純な time shift だけを
primitive data として追加する。

それ以外の量はすべて既存定義から導く。

Global CST 下で `start` が future minimum なら、shift 後の exponent stream は再び
infinite coefficient survivor であり、その survivor defect は exact に

`futureMinimum_localRoofDefect start r`

である。

さらに元の軌道が late tail で `LinearDefectLowerBound K N` を満たすなら、
`N ≤ start` の future minimum から shift した軌道は、十分後
`LinearDefectLowerBound (2*K) R` を満たす。

従って A 型の linear roof escape は future minimum ごとに座標をリセットしても保存される。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
odd-only 軌道を `start` odd steps だけ前へ送る最小の time shift。
-/
def shift
    (O : Collatz3.OddOrbit)
    (start : ℕ) : Collatz3.OddOrbit where
  value n := O.value (start + n)
  exponent n := O.exponent (start + n)
  step n := by
    have h := O.step (start + n)
    simpa [Nat.add_assoc] using h

@[simp] theorem shift_value
    (O : Collatz3.OddOrbit)
    (start n : ℕ) :
    (O.shift start).value n = O.value (start + n) :=
  rfl

@[simp] theorem shift_exponent
    (O : Collatz3.OddOrbit)
    (start n : ℕ) :
    (O.shift start).exponent n = O.exponent (start + n) :=
  rfl

/-- shift 後の segment word は元軌道の対応 segment word そのもの。 -/
theorem shift_segmentWord
    (O : Collatz3.OddOrbit)
    (start i r : ℕ) :
    (O.shift start).segmentWord i r =
      O.segmentWord (start + i) r := by
  induction r generalizing i with
  | zero =>
      simp
  | succ r ih =>
      rw [Collatz3.OddOrbit.segmentWord_succ,
        Collatz3.OddOrbit.segmentWord_succ]
      simp only [shift_exponent]
      rw [ih]
      congr 1

/-- shift prefix depth は元軌道の local segment two-depth。 -/
theorem infinitePrefixDepth_shift_eq_segmentTwoSteps
    (O : Collatz3.OddOrbit)
    (start r : ℕ) :
    infinitePrefixDepth (O.shift start).exponent r =
      Word.twoSteps (O.segmentWord start r) := by
  have h :=
    (O.shift start).twoSteps_segmentWord_zero_eq_infinitePrefixDepth r
  rw [O.shift_segmentWord start 0 r] at h
  simpa using h.symm

/--
Global CST future minimum から見た tail は、それ自身が infinite coefficient survivor。

これは local roof inequality を shift 後の global prefix inequality と読み替えただけである。
-/
theorem shift_isInfiniteCoefficientSurvivor_of_futureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start) :
    (O.shift start).IsInfiniteCoefficientSurvivor := by
  unfold IsInfiniteCoefficientSurvivor IsInfiniteSurvivorExponentStream
  constructor
  · intro r
    simpa using O.exponent_pos (start + r)
  · intro r
    rw [O.infinitePrefixDepth_shift_eq_segmentTwoSteps start r]
    exact
      O.segmentTwoSteps_le_beattyIndex_of_futureMinimum_of_globalCST
        G hStart r

/--
shift 後 survivor defect は fixed-anchor local roof defect と定義的に同じ量。
-/
theorem infiniteSurvivorDefect_shift_eq_localRoofDefect
    (O : Collatz3.OddOrbit)
    (start r : ℕ) :
    infiniteSurvivorDefect (O.shift start).exponent r =
      O.futureMinimum_localRoofDefect start r := by
  unfold infiniteSurvivorDefect futureMinimum_localRoofDefect
  rw [O.infinitePrefixDepth_shift_eq_segmentTwoSteps start r]

/--
late future minimum で shift すると、元の linear defect lower bound は
十分後 `2*K` の linear defect lower bound として再現する。

閾値だけは開始 defect に依存して取り直す。
-/
theorem exists_shift_linearDefectLowerBound_two_mul_of_linearDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N start : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ start)
    (hStart : O.FutureMinimumAt start) :
    ∃ R : ℕ,
      (O.shift start).LinearDefectLowerBound (2 * K) R := by
  obtain ⟨R, hR⟩ :=
    O.exists_localRoofDefect_gt_after_of_linearDefect
      G SInf hLinear hLate hStart
      (infiniteSurvivorDefect O.exponent start)
  refine ⟨R, ?_⟩
  unfold LinearDefectLowerBound
  constructor
  · have hK := hLinear.1
    omega
  · intro r hr
    have hLocal :
        infiniteSurvivorDefect O.exponent start <
          O.futureMinimum_localRoofDefect start r :=
      hR r hr
    have hEndLate : N ≤ start + r := by omega
    have hOrig := hLinear.2 (start + r) hEndLate
    have hExact :=
      O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
        G SInf hStart r
    have hCarry := Critical.beattyCarry_le_one start r
    have hDefectBound :
        infiniteSurvivorDefect O.exponent (start + r) ≤
          2 * O.futureMinimum_localRoofDefect start r := by
      rw [hExact]
      omega
    have hScaled := Nat.mul_le_mul_left K hDefectBound
    rw [O.infiniteSurvivorDefect_shift_eq_localRoofDefect start r]
    calc
      r ≤ start + r := by omega
      _ ≤ K * infiniteSurvivorDefect O.exponent (start + r) := hOrig
      _ ≤ K * (2 * O.futureMinimum_localRoofDefect start r) := hScaled
      _ = (2 * K) * O.futureMinimum_localRoofDefect start r := by ring

/--
Stage 10 のまとめ。

future minimum から shift すると、

* tail は infinite survivor、
* tail defect は local roof defect、
* A 型 linear lower bound は十分後 `2*K` で再び成立する。
-/
theorem futureMinimum_shift_selfSimilarity_of_linearDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N start : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ start)
    (hStart : O.FutureMinimumAt start) :
    (O.shift start).IsInfiniteCoefficientSurvivor ∧
      (∀ r : ℕ,
        infiniteSurvivorDefect (O.shift start).exponent r =
          O.futureMinimum_localRoofDefect start r) ∧
      ∃ R : ℕ,
        (O.shift start).LinearDefectLowerBound (2 * K) R := by
  refine ⟨O.shift_isInfiniteCoefficientSurvivor_of_futureMinimum_of_globalCST G hStart, ?_, ?_⟩
  · intro r
    exact O.infiniteSurvivorDefect_shift_eq_localRoofDefect start r
  · exact
      O.exists_shift_linearDefectLowerBound_two_mul_of_linearDefect
        G SInf hLinear hLate hStart

end OddOrbit
end Collatz3
