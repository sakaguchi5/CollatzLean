import CollatzLean.Collatz2.Canonical.EndpointFloorRecordDescent
import CollatzLean.Collatz2.Geometry.RecordDecomposition

/-!
# RecordFerrers: start index `0` の sanity check

`RankRecordBlock` は block 終端で global chord rank が strict に下がることを要求する。

一方 `FirstCrossing` word では

* cut `0` の signed chord rank は `0`,
* `0 < k ≤ oddSteps w` の signed chord rank は nonnegative

なので、start index `0` から始まる最初の record block は存在できない。

したがって actual FirstCrossing word に対する record decomposition は
`RankRecordDecomposition w 0` では始められない。
既存の current-A record descent と同様、正の start index（典型的には `1`）から
始める必要がある。
-/

namespace Collatz2
namespace Word

/--
FirstCrossing word では start index `0` の rank-record block は存在しない。
-/
private theorem FirstCrossing.no_rankRecordBlock_zero
    {w : Word}
    (hF : FirstCrossing w)
    (R : RankRecordBlock w 0) :
    False := by
  have hEndPos : 0 < R.length := R.length_pos
  have hEndLe : R.length ≤ oddSteps w := by
    simpa using R.next_le_terminal
  have hNonneg :
      0 ≤ chordRankInt w R.length :=
    hF.chordRankInt_nonneg_of_pos_le hEndPos hEndLe
  have hStrict :
      chordRankInt w R.length < 0 := by
    simpa [chordRankInt, prefixTwoDepth] using R.rank_strict
  exact (not_lt_of_ge hNonneg) hStrict

/--
FirstCrossing word では `RankRecordDecomposition w 0` は inhabited にならない。

4A/4B の旧 `startIndex = 0` specialization を actual FirstCrossing へ
直接適用できないことを型の上で明文化する sanity theorem。
-/
theorem FirstCrossing.not_nonempty_rankRecordDecomposition_zero
    {w : Word}
    (hF : FirstCrossing w) :
    ¬ Nonempty (RankRecordDecomposition w 0) := by
  intro hD
  rcases hD with ⟨D⟩
  cases D with
  | terminal block terminal_eq =>
      exact hF.no_rankRecordBlock_zero block
  | step block interior tail =>
      exact hF.no_rankRecordBlock_zero block

/--
FirstCrossing word 上で genuine rank-record decomposition が存在するなら、
その start index は strict positive。
-/
theorem RankRecordDecomposition.startIndex_pos_of_firstCrossing
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hF : FirstCrossing w) :
    0 < a := by
  by_contra hnot
  have ha : a = 0 := by
    omega
  subst a
  exact hF.not_nonempty_rankRecordDecomposition_zero ⟨D⟩

end Word
end Collatz2
