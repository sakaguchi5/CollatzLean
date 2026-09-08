import CollatzLean.Collatz3.Bridge.FirstPassageProfile
import CollatzLean.Collatz3.Critical.RecordFerrers

/-!
# Collatz3: Collatz realization → Critical Ferrers

このファイルが四層目の semantic bridge。

actual first-passage run そのものを Ferrers 定義へ埋め込まず、
既存の lossless bridge

actual run -> word -> finite profile

を経由して、profile の Ferrers view と rank が actual word の prefix data と一致することを導く。
-/

namespace Collatz3

namespace Critical

/-- 任意の word から抽出した profile を ordered Ferrers diagram として読む。 -/
def ferrersFromWord
    (w : Word) :
    Combinatorics.OrderedColumnDiagram (Word.oddSteps w) :=
  ferrersDiagram (profileFromWord w)

/-- word 由来 Ferrers の column height は Beatty roof と prefix depth の差。 -/
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

namespace ActualFirstPassage

/-- actual first-passage 由来 Ferrers profile は admissible。 -/
theorem ferrersProfile_admissible
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.Admissible (Critical.profileFromWord w) :=
  h.extractedProfile_admissible

/-- actual first-passage 由来 Ferrers の checkpoint は元 word の prefix depth に戻る。 -/
theorem ferrersCheckpoint_eq_prefixTwoDepth
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (k : Fin (Word.oddSteps w)) :
    Critical.checkpoint (Critical.profileFromWord w) k =
      Word.prefixTwoDepth w k.1 :=
  h.extractedProfile_checkpoint_eq_prefixTwoDepth k

/--
actual first-passage 由来 profile rank と word rank は、全 relevant cut `k ≤ p` で一致する。
これが Record 分解を profile 側へ移すための基礎 bridge。
-/
theorem profileChordRank_eq_wordChordRank
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y)
    {k : ℕ}
    (hk : k ≤ Word.oddSteps w) :
    Critical.profileChordRank (Critical.profileFromWord w) k =
      Word.criticalChordRank w k := by
  by_cases hlt : k < Word.oddSteps w
  · unfold Critical.profileChordRank Word.criticalChordRank
    rw [Critical.cutDepth_of_lt (Critical.profileFromWord w) hlt]
    rw [Critical.checkpoint_profileFromWord_eq_prefixTwoDepth
      h.critical ⟨k, hlt⟩]
  · have hEq : k = Word.oddSteps w := by omega
    subst k
    rw [Critical.profileChordRank_terminal_eq_zero]
    unfold Word.criticalChordRank
    rw [Word.prefixTwoDepth_oddSteps]
    rw [h.critical.totalTwoDepth_eq]
    ring

/-- actual first-passage の affine numerator は Ferrers profile 側でも元の `B`。 -/
theorem ferrersAffineNumerator_eq_affineConst
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.profileAffineNumerator (Critical.profileFromWord w) =
      Word.affineConst w :=
  h.extractedProfile_affineNumerator_eq_affineConst

end ActualFirstPassage
end Collatz3
