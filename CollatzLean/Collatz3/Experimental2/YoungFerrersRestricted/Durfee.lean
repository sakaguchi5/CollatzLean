import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Area

/-!

# Collatz3 Experimental2: Durfee square と cumulative-width / suffix-drop crossing

width-drop code の block `i` について
* その block の右端までの累積横幅、
* その block に残っている suffix drop height
の小さい方が、その block で対角線まで到達できる最大の正方形候補になる。
従って Durfee size は
`max_i min(cumulativeWidth_i, suffixDrop_i)`
として読むことができる。
RecordFerrers ではこれは
* 経過した canonical block length の累積、
* 残っている rank drop の累積
の crossing size になる。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/--
左から既に `leftWidth` 列進んだ状態を受け取り、
各 plateau の Durfee 候補を並べる。

各 block では、その block の右端までの累積横幅と、
その位置に残る suffix drop height の小さい方を候補とする。
-/
def durfeeCandidatesFrom : ℕ → WidthDropCode → List ℕ
  | _leftWidth, [] => []
  | leftWidth, (r, d) :: cs =>
      min (leftWidth + r) (d + codeDropSum cs) ::
        durfeeCandidatesFrom (leftWidth + r) cs

/-- 左端、すなわち既通過横幅 `0` から読む Durfee crossing candidates。 -/
def durfeeCandidates (c : WidthDropCode) : List ℕ :=
  durfeeCandidatesFrom 0 c

/-- 候補列の最大値。空 code では `0`。 -/
def maxNatList : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (maxNatList xs)

/-- width-drop code の Durfee size。 -/
def codeDurfeeSize (c : WidthDropCode) : ℕ :=
  maxNatList (durfeeCandidates c)

/--
Durfee size は累積横幅と suffix drop の
crossing 候補の最大値そのもの。

定義を公開 theorem として固定する。
-/
theorem codeDurfeeSize_eq_cumulativeWidthSuffixCrossing
    (c : WidthDropCode) :
    codeDurfeeSize c =
      maxNatList (durfeeCandidatesFrom 0 c) := by
  rfl

/-- 空図形の Durfee size は `0`。 -/
@[simp] theorem codeDurfeeSize_nil :
    codeDurfeeSize [] = 0 := rfl

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/--
RecordFerrers rank-envelope の Durfee size。

canonical block length の累積横幅と
suffix rank defect の crossing を一数値へ圧縮する。
-/
def rankDurfeeSize
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : ℕ :=
  codeDurfeeSize R.plateauWidthDropCode

/--
RecordFerrers の Durfee size は canonical width/rank-drop code の

cumulative-width / suffix-drop crossing 公式で exact に与えられる。
-/
theorem rankDurfeeSize_eq_crossing
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.rankDurfeeSize =
      maxNatList
        (durfeeCandidatesFrom 0 R.plateauWidthDropCode) := by
  rfl

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
