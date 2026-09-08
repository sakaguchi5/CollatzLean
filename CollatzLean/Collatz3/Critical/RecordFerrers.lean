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
-/

namespace Collatz3
namespace Critical
namespace RecordFerrers

/--
critical profile 上の一つの record block。

profile から得られる rank 関数について、
一般の `Combinatorics.IsRecordBlock` を満たし、
さらに block の終点が profile の終端 `m` を越えないことを要求する。

ここでは admissibility や actual Collatz 軌道の情報は持たせない。
-/
def IsBlock
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  a + r ≤ m ∧
    Combinatorics.IsRecordBlock (profileChordRank h) a r

namespace IsBlock

/-- Record-Ferrers block の終点は profile の終端を越えない。 -/
theorem end_le_terminal
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsBlock h a r) :
    a + r ≤ m :=
  B.1

/--
Record-Ferrers block から、
その背後にある一般の record block を取り出す。
-/
theorem record
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (B : IsBlock h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r :=
  B.2

end IsBlock

/--
record skeleton が critical profile 全体を、
開始点 `0` から終端 `m` までちょうど覆うことを表す。

ここで要求するのは、

* skeleton の総長が profile 幅 `m` に一致すること
* profile の rank 関数上で、開始点 `0` から
  一般の record realization を与えること

だけである。

admissibility や actual Collatz 軌道の情報は定義に埋め込まない。
-/
def Realizes
    {m : ℕ}
    (h : Profile m)
    (S : Combinatorics.RecordSkeleton) : Prop :=
  S.totalLength = m ∧
    S.RealizesFrom (profileChordRank h) 0

namespace Realizes

/--
Record-Ferrers realization の skeleton の総長は、
profile の幅 `m` に一致する。
-/
theorem totalLength_eq
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S) :
    S.totalLength = m :=
  R.1

/--
Record-Ferrers realization から、
profile の rank 関数上の一般の record realization を取り出す。
-/
theorem record_realization
    {m : ℕ}
    {h : Profile m}
    {S : Combinatorics.RecordSkeleton}
    (R : Realizes h S) :
    S.RealizesFrom (profileChordRank h) 0 :=
  R.2

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
