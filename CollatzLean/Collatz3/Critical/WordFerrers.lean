import CollatzLean.Collatz3.Critical.Ferrers
import CollatzLean.Collatz3.Critical.ProfileExtraction

/-!
# Collatz3: Word の pure critical Ferrers view

word から profile / ordered diagram / chord rank を読む pure view。
actual `Runs` や `ActualFirstPassage` は import しない。

lossless な profile checkpoint 復元は `CriticalFirstPassage` 条件下の theorem であり、
このファイルの定義そのものに actuality を埋め込まない。
-/

namespace Collatz3

namespace Critical

/-- 任意の word から抽出した profile を ordered column diagram として読む。 -/
def ferrersFromWord
    (w : Word) :
    Combinatorics.OrderedColumnDiagram (Word.oddSteps w) :=
  ferrersDiagram (profileFromWord w)

/-- word 由来 ordered diagram の列高は Beatty roof と prefix depth の差。 -/
@[simp] theorem ferrersFromWord_height
    (w : Word)
    (k : Fin (Word.oddSteps w)) :
    ferrersFromWord w k =
      beattyIndex k.1 - Word.prefixTwoDepth w k.1 := by
  rfl

end Critical

namespace Word

/--
critical terminal depth を基準にした word 側 chord rank。
actual orbit 値は使わず prefix two-depth だけから作る。
-/
def criticalChordRank
    (w : Word)
    (k : ℕ) : ℤ :=
  (Critical.criticalTwoDepth (oddSteps w) : ℤ) * (k : ℤ) -
    (oddSteps w : ℤ) * (prefixTwoDepth w k : ℤ)

end Word
end Collatz3
