import CollatzLean.CollatzSecondLayer3.FirstCrossingReturnArithmetic
import CollatzLean.CollatzSecondLayer3.FutureMinimumHighEvent

/-!
# consecutive future-minimumを跨ぐactual geometry

標準`futureMinIndex`では次項が`current+1`以後のtail minimumそのものなので、
current future-minimumからのfirst-crossing endpointより次future-minimum値は小さい。

その値差`Δ`はactual first-crossing return gap`d`以下であり、
両future-minimumの指数がexactに1であることから`4 ∣ Δ`。
従って`4 ≤ Δ ≤ d`を得る。

また次future-minimumより前の任意のactual位置から次minimumまでのsuffixは
値を真に下げるためpure contractingである。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 標準future-minimum列の隣接値差。 -/
noncomputable def consecutiveFutureMinimumValueGap
    (O : OddOrbit) (j : ℕ) : ℕ :=
  O.value (O.futureMinIndex (j + 1)) -
    O.value (O.futureMinIndex j)

/-- 標準future-minimum列の隣接位置差。 -/
noncomputable def consecutiveFutureMinimumIndexGap
    (O : OddOrbit) (j : ℕ) : ℕ :=
  O.futureMinIndex (j + 1) - O.futureMinIndex j

/--
次の標準future-minimum値は、currentからの任意の正長endpoint以下。
-/
theorem nextFutureMinimumValue_le_positiveEndpoint
    (O : OddOrbit)
    (j p : ℕ)
    (hp : 0 < p) :
    O.value (O.futureMinIndex (j + 1)) ≤
      O.value (O.futureMinIndex j + p) := by
  change
    O.value (O.tailMinIndex (O.futureMinIndex j + 1)) ≤
      O.value (O.futureMinIndex j + p)
  rw [O.value_tailMinIndex]
  exact O.tailMinValue_le
    (O.futureMinIndex j + 1)
    (O.futureMinIndex j + p)
    (by omega)

/-- 非有界軌道では隣接future-minimum値差は正。 -/
theorem consecutiveFutureMinimumValueGap_pos
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) :
    0 < consecutiveFutureMinimumValueGap O j := by
  unfold consecutiveFutureMinimumValueGap
  exact Nat.sub_pos_of_lt (O.futureMinValue_lt_succ hU j)

/--
隣接future-minimum値差はcurrent first-crossingのactual return gap以下。
-/
theorem consecutiveFutureMinimumValueGap_le_firstCrossingReturnGap
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j p : ℕ)
    (hC : FirstCrossingAt O (O.futureMinIndex j) p) :
    consecutiveFutureMinimumValueGap O j ≤
      firstCrossingReturnGap (O := O) (O.futureMinIndex j) p := by
  have hp : 0 < p := hC.length_pos
  have hstartNext :
      O.value (O.futureMinIndex j) <
        O.value (O.futureMinIndex (j + 1)) :=
    O.futureMinValue_lt_succ hU j
  have hnextEnd :
      O.value (O.futureMinIndex (j + 1)) ≤
        O.value (O.futureMinIndex j + p) :=
    nextFutureMinimumValue_le_positiveEndpoint O j p hp
  unfold consecutiveFutureMinimumValueGap firstCrossingReturnGap
  omega

/--
指数1の二位置で値が増えているなら、その値差は4の倍数。
-/
theorem four_dvd_value_gap_of_exponent_one
    (O : OddOrbit)
    {i j : ℕ}
    (hij : O.value i < O.value j)
    (hei : O.exponent i = 1)
    (hej : O.exponent j = 1) :
    ∃ q : ℕ, O.value j - O.value i = 4 * q := by
  have hsi :
      2 * O.value (i + 1) = 3 * O.value i + 1 := by
    simpa [hei] using O.step i
  have hsj :
      2 * O.value (j + 1) = 3 * O.value j + 1 := by
    simpa [hej] using O.step j
  rcases O.value_odd (i + 1) with ⟨a, ha⟩
  rcases O.value_odd (j + 1) with ⟨b, hb⟩
  rw [ha] at hsi
  rw [hb] at hsj
  have hab : a < b := by
    omega
  let d := O.value j - O.value i
  let t := b - a
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have htPos : 0 < t := by
    dsimp [t]
    omega
  have hrelation : 3 * d = 4 * t := by
    dsimp [d, t]
    omega
  have htd : t < d := by
    omega
  refine ⟨d - t, ?_⟩
  dsimp [d, t] at hrelation htd ⊢
  omega

/-- 隣接標準future-minimum値差は4の正倍数。 -/
theorem four_dvd_consecutiveFutureMinimumValueGap
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) :
    ∃ q : ℕ,
      consecutiveFutureMinimumValueGap O j = 4 * q := by
  have hlt := O.futureMinValue_lt_succ hU j
  have hmin0 := O.futureMinimumAt_futureMinIndex j
  have hmin1 := O.futureMinimumAt_futureMinIndex (j + 1)
  have he0 := futureMinimum_exponent_eq_one_of_unbounded O hU hmin0
  have he1 := futureMinimum_exponent_eq_one_of_unbounded O hU hmin1
  simpa [consecutiveFutureMinimumValueGap] using
    four_dvd_value_gap_of_exponent_one O hlt he0 he1

/-- 隣接標準future-minimum値差は少なくとも4。 -/
theorem four_le_consecutiveFutureMinimumValueGap
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) :
    4 ≤ consecutiveFutureMinimumValueGap O j := by
  obtain ⟨q, hq⟩ := four_dvd_consecutiveFutureMinimumValueGap O hU j
  have hpos := consecutiveFutureMinimumValueGap_pos O hU j
  rw [hq] at hpos ⊢
  have hqPos : 0 < q := by omega
  omega

/--
標準future-minimum first-crossingのactual return gapは少なくとも4。
-/
theorem four_le_firstCrossingReturnGap_at_futureMinIndex
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j p : ℕ)
    (hC : FirstCrossingAt O (O.futureMinIndex j) p) :
    4 ≤ firstCrossingReturnGap (O := O) (O.futureMinIndex j) p := by
  exact le_trans
    (four_le_consecutiveFutureMinimumValueGap O hU j)
    (consecutiveFutureMinimumValueGap_le_firstCrossingReturnGap
      O hU j p hC)

/--
標準future-minimum first-crossingはsharp return boundと`d≥4`から長さ13以上。
-/
theorem thirteen_le_firstCrossingLength_at_futureMinIndex
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j p : ℕ)
    (hC : FirstCrossingAt O (O.futureMinIndex j) p) :
    13 ≤ p := by
  let d := firstCrossingReturnGap (O := O) (O.futureMinIndex j) p
  have hd : 4 ≤ d := by
    simpa [d] using four_le_firstCrossingReturnGap_at_futureMinIndex O hU j p hC
  have hsharp : 3 * d < p := by
    simpa [d] using
      three_mul_firstCrossingReturnGap_lt_length
        (O.futureMinimumAt_futureMinIndex j)
        hC
  omega

/--
actual segmentが値を真に下げるなら、その指数語はpure contracting。
-/
theorem segmentWord_contracting_of_value_decrease
    (O : OddOrbit)
    {i q : ℕ}
    (hq : 0 < q)
    (hdec : O.value (i + q) < O.value i) :
    Contracting (O.segmentWord i q) := by
  let w := O.segmentWord i q
  have hvalid : Valid w := (O.runs_segment i q).valid
  have hne : w ≠ [] := by
    intro hw
    have hlen := congrArg List.length hw
    have hq0 : q = 0 := by
      simpa [w] using hlen
    omega
  rcases expanding_or_contracting_of_valid_nonempty hvalid hne with hE | hC
  · have hrun :
        2 ^ twoSteps w * O.value (i + q) =
          3 ^ q * O.value i + affineConst w := by
      simpa [w, Realizes, oddSteps] using O.realizes_segment i q
    have hscale : 2 ^ twoSteps w < 3 ^ q := by
      simpa [w, Expanding, oddSteps] using hE
    have hyPos : 0 < O.value (i + q) := O.value_pos (i + q)
    have hxPos : 0 < O.value i := O.value_pos i
    have hleft :
        2 ^ twoSteps w * O.value (i + q) <
          3 ^ q * O.value i := by
      calc
        2 ^ twoSteps w * O.value (i + q)
            < 3 ^ q * O.value (i + q) :=
          (Nat.mul_lt_mul_right hyPos).2 hscale
        _ < 3 ^ q * O.value i :=
          (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2 hdec
    have hright :
        3 ^ q * O.value i ≤
          2 ^ twoSteps w * O.value (i + q) := by
      rw [hrun]
      omega
    exact False.elim ((Nat.not_lt_of_ge hright) hleft)
  · exact hC

/--
current標準future-minimumと次minimumの間にある任意の位置から、
次minimumまでのsuffixはcontracting。
-/
theorem suffix_to_nextFutureMinimum_contracting
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j t : ℕ)
    (hleft : O.futureMinIndex j < t)
    (hright : t < O.futureMinIndex (j + 1)) :
    Contracting
      (O.segmentWord t (O.futureMinIndex (j + 1) - t)) := by
  let a := O.futureMinIndex j
  let b := O.futureMinIndex (j + 1)
  have htail :
      O.value b ≤ O.value t := by
    change O.value (O.tailMinIndex (a + 1)) ≤ O.value t
    rw [O.value_tailMinIndex]
    exact O.tailMinValue_le (a + 1) t (by omega)
  have hne : O.value t ≠ O.value b := by
    exact O.value_ne_of_lt_of_unbounded hU hright
  have hdec : O.value b < O.value t := by
    omega
  have hlenPos : 0 < b - t := by
    omega
  have hend : t + (b - t) = b := by
    omega
  have hcontract :
      Contracting (O.segmentWord t (b - t)) := by
    apply segmentWord_contracting_of_value_decrease
      O
      (i := t)
      (q := b - t)
    · exact hlenPos
    · rw [hend]
      exact hdec
  simpa [b] using hcontract

/--
次future-minimumがfirst-crossing endpointより前に来る場合、
current→next minimumのwhole wordはfirst-crossingのproper expanding prefix。
-/
theorem current_to_nextFutureMinimum_expanding_of_before_crossing
    (O : OddOrbit)
    (j p : ℕ)
    (hC : FirstCrossingAt O (O.futureMinIndex j) p)
    (hbefore : O.futureMinIndex (j + 1) < O.futureMinIndex j + p) :
    Expanding
      (O.segmentWord
        (O.futureMinIndex j)
        (consecutiveFutureMinimumIndexGap O j)) := by
  let a := O.futureMinIndex j
  let b := O.futureMinIndex (j + 1)
  let m := consecutiveFutureMinimumIndexGap O j
  have hab : a < b := O.futureMinIndex_lt_succ j
  have hmPos : 0 < m := by
    dsimp [m, consecutiveFutureMinimumIndexGap, a, b]
    omega
  have hmLt : m < p := by
    dsimp [m, consecutiveFutureMinimumIndexGap, a, b]
    omega
  have hpref := hC.properExpanding m hmPos (by simpa using hmLt)
  have hmLe : m ≤ p := Nat.le_of_lt hmLt
  rw [O.segmentWord_take_of_le hmLe] at hpref
  simpa [a, m] using hpref

end CollatzSecondLayer3
