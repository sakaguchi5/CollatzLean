import CollatzLean.Collatz2.CSTMicro.BeattyPositions

/-!
# First-passage crossing length = Beatty index + 1

first-passage word `v` の endpoint odd count を `m` とすると、

  v.length - 1 = floor (m * log₂ 3)

を exact power form で証明する。

実数 log は使わず、右辺は `beattyIndex m`。
したがって実際に現れる first-passage length は
endpoint count だけで一意に決まる。
-/

namespace Collatz2
namespace CSTMicro

/-- endpoint odd count に対応する critical crossing length。 -/
def criticalCrossingLength (m : ℕ) : ℕ :=
  beattyIndex m + 1

/--
first-passage word の最後の proper time `k-1` は
endpoint odd count の Beatty index。
-/
theorem firstPassage_length_pred_eq_beattyIndex_endpointOddCount
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    v.length - 1 = beattyIndex (oddCount v) := by
  have hkPos : 0 < v.length := List.length_pos_of_ne_nil h.1
  let e := v.length - 1
  let m := oddCount v
  have heSucc : e + 1 = v.length := by
    simp [e]
    omega
  have hUpper : 3 ^ m ≤ 2 ^ (e + 1) := by
    have hterm := h.2.2
    unfold CoefficientContracting at hterm
    rw [heSucc]
    exact le_of_lt hterm
  have hBeattyLe : beattyIndex m ≤ e :=
    beattyIndex_le_of_upper hUpper
  have hELe : e ≤ beattyIndex m := by
    by_contra hnot
    have hlt : beattyIndex m < e := by omega
    have hqSuccLe : beattyIndex m + 1 ≤ e := by omega
    by_cases he0 : e = 0
    · omega
    · have hePos : 0 < e := Nat.pos_of_ne_zero he0
      have heLt : e < v.length := by
        rw [← heSucc]
        omega
      have hExp := h.2.1 e hePos heLt
      unfold CoefficientExpandingAt at hExp
      have hPow :
          2 ^ (beattyIndex m + 1) ≤ 2 ^ e :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hqSuccLe
      have hBeattyUpper := beattyIndex_upper m
      have hPrefixLe :
          prefixOddCount v e ≤ m := by
        simpa [m] using prefixOddCount_le_oddCount v e
      have hThreeLe :
          3 ^ prefixOddCount v e ≤ 3 ^ m := by
        exact
          Nat.pow_le_pow_right
            (by omega : 0 < (3 : ℕ))
            hPrefixLe
      have hExpM :
          2 ^ e < 3 ^ m := by
        exact lt_of_lt_of_le hExp hThreeLe
      have hUpperE :
          3 ^ m ≤ 2 ^ e := by
        exact le_trans hBeattyUpper hPow
      exact (not_lt_of_ge hUpperE) hExpM
  have heq : e = beattyIndex m :=
    Nat.le_antisymm hELe hBeattyLe
  simpa [e, m] using heq

/-- first-passage length は endpoint count の critical crossing length。 -/
theorem firstPassage_length_eq_criticalCrossingLength
    {v : ParityWord}
    (h : IsFirstPassageWord v) :
    v.length = criticalCrossingLength (oddCount v) := by
  have hkPos : 0 < v.length := List.length_pos_of_ne_nil h.1
  have hpred :=
    firstPassage_length_pred_eq_beattyIndex_endpointOddCount h
  unfold criticalCrossingLength
  omega

/-- FirstPassagePath 版。 -/
theorem FirstPassagePath.length_pred_eq_beattyIndex_endpointOddCount
    (P : FirstPassagePath) :
    P.length - 1 = beattyIndex P.endpointOddCount := by
  simpa [FirstPassagePath.length, FirstPassagePath.endpointOddCount] using
    firstPassage_length_pred_eq_beattyIndex_endpointOddCount
      P.isFirstPassageWord

/-- FirstPassagePath の length も endpoint count だけで決まる。 -/
theorem FirstPassagePath.length_eq_criticalCrossingLength
    (P : FirstPassagePath) :
    P.length = criticalCrossingLength P.endpointOddCount := by
  simpa [FirstPassagePath.length, FirstPassagePath.endpointOddCount] using
    firstPassage_length_eq_criticalCrossingLength
      P.isFirstPassageWord

/--
Ferrers boundary の最後の proper index も Beatty index。
critical Sturmian 同定との直接 bridge。
-/
theorem ferrersBoundary_length_pred_eq_beattyIndex_oddCount
    {v : ParityWord}
    (h : IsFerrersBoundary v) :
    v.length - 1 = beattyIndex (oddCount v) := by
  exact firstPassage_length_pred_eq_beattyIndex_endpointOddCount h.1

/--
critical boundary の n 番目の one は `beattyIndex n` にある。
`n < endpoint odd count` ならその位置は terminal より前。
-/
theorem criticalBoundary_nth_one_before_terminal
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    {n : ℕ}
    (hn : n < oddCount v) :
    beattyIndex n < v.length - 1 := by
  have hend :=
    firstPassage_length_pred_eq_beattyIndex_endpointOddCount h
  have hmono := beattyIndex_strictMono hn
  rw [hend]
  exact hmono

/--
canonical critical boundary 上で、n 番目の one の直前/直後 height は n/n+1。
-/
theorem criticalBoundary_nth_one_prefix_heights
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    {n : ℕ}
    (hn : n < oddCount v) :
    prefixOddCount
        (criticalBoundaryWord v.length)
        (beattyIndex n) = n ∧
      prefixOddCount
        (criticalBoundaryWord v.length)
        (beattyIndex n + 1) = n + 1 := by
  have hkPos : 0 < v.length := List.length_pos_of_ne_nil h.1
  have hpos := criticalBoundary_nth_one_before_terminal h hn
  constructor
  · rw [criticalBoundaryWord_prefixOddCount hkPos (by omega)]
    exact criticalPrefixHeight_beattyIndex n
  · rw [criticalBoundaryWord_prefixOddCount hkPos (by omega)]
    exact (beattyIndex_is_nth_critical_one n).2

end CSTMicro
end Collatz2
