import CollatzLean.Collatz2.ObstructionAudit.ExactWordTranslation
import CollatzLean.Collatz2.Canonical.SwapCarry
import CollatzLean.Collatz2.Canonical.Replay


/-!
# Collatz2 Obstruction Audit: weak consequences of exact word translation

`ExactWordTranslationConstraints` から full trajectory argument を直ちに行わず、
より薄い genuine-word consequences を取り出す。

* whole block の replay coordinate
* actual prefix の replay / canonical residue compatibility
* affineConst の prefix/suffix recursion
* adjacent word swap の exact 0/1 carry equation

word swap / carry はもはや `Synthesis` を介さず、`Word` の canonical residue
geometry と displacement separation の直接の corollary として利用する。
-/

namespace Collatz2
namespace ObstructionAudit
namespace ExactWordTranslationConstraints

/-- exact block は追加仮定なしで replay coordinate を持つ。 -/
def replayCoordinate
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Word.ReplayCoordinate
      (P.word n)
      (P.startValue n)
      (P.startValue (n + 1)) :=
  Word.ReplayCoordinate.ofRuns (P.runs n) (P.word_nonempty n)

/--
word を `u ++ v` に切ると actual prefix endpoint と prefix replay coordinate が存在する。
-/
theorem exists_prefix_replay
    (P : ExactWordTranslationConstraints)
    (n : ℕ)
    {u v : Word}
    (hdecomp : P.word n = u ++ v)
    (hune : u ≠ []) :
    ∃ y : ℕ,
      Runs u (P.startValue n) y ∧
      Nonempty (Word.ReplayCoordinate u (P.startValue n) y) := by
  have hrun :
      Runs (u ++ v) (P.startValue n) (P.startValue (n + 1)) := by
    rw [← hdecomp]
    exact P.runs n
  obtain ⟨y, hu, _hv⟩ := Runs.split_append hrun
  exact ⟨y, hu, ⟨Word.ReplayCoordinate.ofRuns hu hune⟩⟩

/--
actual nonempty prefix に対して whole start はその prefix の canonical residue class に属する。
-/
theorem prefix_start_mod_eq_canonicalStart
    (P : ExactWordTranslationConstraints)
    (n : ℕ)
    {u v : Word}
    (hdecomp : P.word n = u ++ v)
    (hune : u ≠ []) :
    P.startValue n % Word.residueModulus u =
      Word.canonicalStart u := by
  obtain ⟨y, hu, _⟩ := P.exists_prefix_replay n hdecomp hune
  exact hu.realizes.start_mod_eq_canonicalStart (hu.end_odd_of_ne_nil hune)

/-- exact block の affine translation は任意の prefix/suffix cut で append recursion を満たす。 -/
theorem affineConst_split
    (P : ExactWordTranslationConstraints)
    (n : ℕ)
    {u v : Word}
    (hdecomp : P.word n = u ++ v) :
    Word.affineConst (P.word n) =
      3 ^ Word.oddSteps v * Word.affineConst u +
        2 ^ Word.twoSteps u * Word.affineConst v := by
  rw [hdecomp, Word.affineConst_append]

/--
adjacent packet words の canonical starts は word-swap displacement と0/1 carry の exact equation を満たす。
-/
theorem adjacent_swapCarry_spec
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Word.canonicalStart (P.word (n + 1) ++ P.word n) +
        Word.swapResidueDisplacement (P.word n) (P.word (n + 1)) =
      Word.canonicalStart (P.word n ++ P.word (n + 1)) +
        Word.swapCarry (P.word n) (P.word (n + 1)) *
          Word.residueModulus (P.word n ++ P.word (n + 1)) := by
  exact Word.swapCarry_spec (P.word n) (P.word (n + 1))

/-- adjacent swap carry は常に0または1。 -/
theorem adjacent_swapCarry_eq_zero_or_one
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Word.swapCarry (P.word n) (P.word (n + 1)) = 0 ∨
      Word.swapCarry (P.word n) (P.word (n + 1)) = 1 := by
  exact Word.swapCarry_eq_zero_or_one (P.word n) (P.word (n + 1))

end ExactWordTranslationConstraints
end ObstructionAudit
end Collatz2
