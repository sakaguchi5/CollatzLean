import CollatzLean.Collatz2.ObstructionAudit.ConstraintPackets
import CollatzLean.Collatz2.Orbit.RealizationRecovery
import CollatzLean.Collatz2.Canonical.Representative

/-!
# Collatz2 Obstruction Audit: exact word-translation boundary

`DiagonalWordProfileConstraints` は diagonal `3^p / 2^H` と
word profile までは genuine にするが、translation を自由にしている。

ここでは最後の境界

  `translate n = Word.affineConst (word n)`

を追加する。

この条件を加えると packet の affine equation は genuine `Word.Realizes` になり、
validity と odd endpoint から `Runs` まで復元される。
したがってこれは単なる弱い算術 packet ではなく actual dynamics への境界 marker である。
-/

namespace Collatz2
namespace ObstructionAudit

/-- diagonal word profile に genuine affine translation を追加した exact packet。 -/
structure ExactWordTranslationConstraints extends DiagonalWordProfileConstraints where
  translate_eq_affineConst : ∀ n,
    translate n = Word.affineConst (word n)

namespace ExactWordTranslationConstraints

/-- exact translation を入れると各 block の affine equation は genuine word realization。 -/
theorem realizes_word
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Word.Realizes (P.word n) (P.startValue n) (P.startValue (n + 1)) := by
  have h := P.realizes n
  rw [P.twoCoeff_eq_word n, P.oddCoeff_eq_word n,
    P.translate_eq_affineConst n] at h
  simpa [Word.Realizes, AffineTransfer.Realizes,
    AffineTransfer.ofWord] using h

/-- packet endpoint は `4m+3` なので odd。 -/
theorem end_odd
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Odd (P.startValue (n + 1)) := by
  refine ⟨2 * P.coordinate (n + 1) + 1, ?_⟩
  rw [P.start_coordinate (n + 1)]
  ring

/-- exact packet の各 block は stepwise normalized `Runs` を持つ。 -/
theorem runs
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    Runs (P.word n) (P.startValue n) (P.startValue (n + 1)) := by
  exact
    (P.realizes_word n).toRuns_of_valid_of_end_odd
      (P.word_valid n)
      (P.end_odd n)

/-- exact packet は各 start を genuine canonical residue class に置く。 -/
theorem start_mod_eq_canonicalStart
    (P : ExactWordTranslationConstraints)
    (n : ℕ) :
    P.startValue n % Word.residueModulus (P.word n) =
      Word.canonicalStart (P.word n) := by
  exact (P.realizes_word n).start_mod_eq_canonicalStart (P.end_odd n)

end ExactWordTranslationConstraints
end ObstructionAudit
end Collatz2
