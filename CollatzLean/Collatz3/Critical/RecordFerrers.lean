import CollatzLean.Collatz3.Critical.Ferrers
import CollatzLean.Collatz3.Combinatorics.Record

/-!
# Collatz3: Record Ferrers

ここでは新しい図形 structure を作らない。

* 図形本体: `Critical.Profile` の `ferrersDiagram` view
* record 一般論: `Combinatorics.RecordSkeleton`
* Collatz-critical 固有の接着: `profileChordRank` を generic record predicate に渡す

という三者を薄い predicate で結ぶ。
actual Collatz run はこのファイルには入れず、Bridge 層に残す。

重要な修正として、profile terminal `m` を strict record block の終点にはしない。
strict record blocks は proper cut までで止め、その後を terminal tail として分離する。
-/

namespace Collatz3
namespace Critical
namespace RecordFerrers

/--
critical profile 上の一つの proper record block。

profile から得られる rank 関数について一般の `Combinatorics.IsRecordBlock` を満たし、
block endpoint が profile terminal `m` より strict に手前であることを要求する。

ここでは admissibility や actual Collatz 軌道の情報は持たせない。
-/
def IsBlock
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  a + r < m ∧
    Combinatorics.IsRecordBlock (profileChordRank h) a r

namespace IsBlock

/-- Record-Ferrers block の終点は terminal より手前。 -/
theorem end_lt_terminal
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsBlock h a r) :
    a + r < m :=
  B.1

/-- 互換用の弱い境界。 -/
theorem end_le_terminal
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsBlock h a r) :
    a + r ≤ m :=
  Nat.le_of_lt B.end_lt_terminal

/-- Record-Ferrers block の背後にある generic record block。 -/
theorem recordBlock
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsBlock h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r :=
  B.2

end IsBlock

/--
record skeleton が proper record cuts を開始点 `0` から順に実現し、
最後の record cut から terminal `m` までを closing tail として残す。

`m > 0` なら skeleton の総長は `m` より strict に小さい。
`m = 0` だけは退化ケースとして許す。

terminal tail interior には最後の record rank より低い点がないが、
terminal endpoint 自身を新しい strict record low とは要求しない。
-/
def Realizes
    {m : ℕ}
    (h : Profile m)
    (S : Combinatorics.RecordSkeleton) : Prop :=
  (S.totalLength < m ∨ m = 0) ∧
    S.RealizesFrom (profileChordRank h) 0 ∧
    Combinatorics.IsTerminalTail
      (profileChordRank h) S.totalLength m

namespace Realizes

/-- 非空 profile では最後の record cut は terminal より手前。 -/
theorem totalLength_lt_terminal
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S)
    (hm : 0 < m) :
    S.totalLength < m := by
  rcases R.1 with hlt | hm0
  · exact hlt
  · omega

/-- Record-Ferrers realization の generic record skeleton 部分。 -/
theorem record_realization
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S) :
    S.RealizesFrom (profileChordRank h) 0 :=
  R.2.1

/-- Record-Ferrers realization の closing terminal tail。 -/
theorem terminal_tail
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S) :
    Combinatorics.IsTerminalTail
      (profileChordRank h) S.totalLength m :=
  R.2.2

/-- terminal tail の start cut は terminal を越えない。 -/
theorem totalLength_le_terminal
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S) :
    S.totalLength ≤ m :=
  R.terminal_tail.start_le_terminal

/--
旧い「skeleton が terminal まで strict record blocks だけで全覆いする」形は、
非空 profile の新しい realization では起こらない。
-/
theorem totalLength_ne_terminal_of_pos
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S)
    (hm : 0 < m) :
    S.totalLength ≠ m := by
  exact Nat.ne_of_lt (R.totalLength_lt_terminal hm)

end Realizes

/--
`Admissible h` と `Realizes h S` を必要な theorem 側で組み合わせるための単なる略記。
新しい情報を保存する structure にはしない。
-/
def AdmissibleRealizes
    {m : ℕ}
    (h : Profile m)
    (S : Combinatorics.RecordSkeleton) : Prop :=
  Admissible h ∧ Realizes h S

end RecordFerrers
end Critical
end Collatz3
