import CollatzLean.Collatz2.ObstructionAudit.ExactWordTranslation
import CollatzLean.Collatz2.ObstructionAudit.CanonicalResidueAudit
import CollatzLean.Collatz2.Core.TranslationPath

/-!
# Collatz2 Obstruction Audit: genuine translation の薄い shadows

exact word translation `translate = Word.affineConst word` を一個の opaque boundary とせず、
displacement-form constant が持つ弱い consequence を独立に監査する。

ここでは特に

* endpoint 側 translation congruence modulo `2*C`
* Archimedean path-size bound `B < A*C`

を切り出す。既存 canonical-residue witness は start-side residue は保つが、
block 0 ですでにこの二条件を破る。
-/

namespace Collatz2
namespace ObstructionAudit

/--
The free translation has the same endpoint-side local shadow as the genuine
word translation.
-/
def EndpointTranslationShadow
    (P : DiagonalWordProfileConstraints) : Prop :=
  ∀ n : ℕ,
    P.translate n % (2 * P.oddCoeff n) =
      Word.affineConst (P.word n) % (2 * P.oddCoeff n)

/-- Genuine word translation satisfies the endpoint-side shadow trivially. -/
theorem ExactWordTranslationConstraints.endpointTranslationShadow
    (P : ExactWordTranslationConstraints) :
    EndpointTranslationShadow P.toDiagonalWordProfileConstraints := by
  intro n
  rw [P.translate_eq_affineConst n]

/--
Archimedean size shadow of a genuine word translation.
This is much weaker than exact equality.
-/
def TranslationSizeShadow
    (P : DiagonalWordProfileConstraints) : Prop :=
  ∀ n : ℕ,
    P.translate n < P.twoCoeff n * P.oddCoeff n

/-- Every exact word-translation packet satisfies the path-size shadow. -/
theorem ExactWordTranslationConstraints.translationSizeShadow
    (P : ExactWordTranslationConstraints) :
    TranslationSizeShadow P.toDiagonalWordProfileConstraints := by
  intro n
  rw [P.translate_eq_affineConst n,
    P.twoCoeff_eq_word n, P.oddCoeff_eq_word n]
  simpa [AffineTransfer.ofWord] using
    Word.ofWord_translate_lt_diagonal_product (P.word n)

namespace CanonicalResidueModel

/--
The canonical-residue witness already fails the endpoint-side translation
shadow at its first block.
-/
theorem endpointTranslationShadow_fails_zero :
    translate 0 % (2 * oddCoeff 0) ≠
      Word.affineConst (word 0) % (2 * oddCoeff 0) := by
  norm_num [translate, oddCoeff, word, Word.affineConst]
  decide

/-- Hence the existing canonical-residue packet does not satisfy that shadow. -/
theorem not_endpointTranslationShadow :
    ¬ EndpointTranslationShadow diagonalPacket := by
  intro h
  have h0 := h 0
  change
    translate 0 % (2 * oddCoeff 0) =
      Word.affineConst (word 0) % (2 * oddCoeff 0) at h0
  exact endpointTranslationShadow_fails_zero h0

/-- The same witness also violates the genuine translation size bound at zero. -/
theorem translationSizeShadow_fails_zero :
    ¬ translate 0 < twoCoeff 0 * oddCoeff 0 := by
  norm_num [translate, twoCoeff, oddCoeff]
  decide

/-- Hence the existing canonical-residue packet also fails the size shadow. -/
theorem not_translationSizeShadow :
    ¬ TranslationSizeShadow diagonalPacket := by
  intro h
  have h0 := h 0
  change translate 0 < twoCoeff 0 * oddCoeff 0 at h0
  exact translationSizeShadow_fails_zero h0

end CanonicalResidueModel
end ObstructionAudit
end Collatz2
