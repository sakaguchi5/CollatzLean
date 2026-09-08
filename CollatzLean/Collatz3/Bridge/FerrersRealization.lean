import CollatzLean.Collatz3.Bridge.FirstPassageProfile
import CollatzLean.Collatz3.Critical.WordFerrers

/-!
# Collatz3: actual Collatz realization → pure critical Ferrers rank

このファイルには pure Word/Ferrers 定義を置かない。

actual first-passage run
  -> extracted finite profile
  -> pure Word/Profile chord rank

という既存の lossless bridge だけを接続する。
-/

namespace Collatz3
namespace ActualFirstPassage

/--
actual first-passage 由来 profile rank と word rank は、全 relevant cut `k ≤ p` で一致する。
これが record decomposition を actual word と pure profile の間で輸送する基礎 bridge。
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

end ActualFirstPassage
end Collatz3
