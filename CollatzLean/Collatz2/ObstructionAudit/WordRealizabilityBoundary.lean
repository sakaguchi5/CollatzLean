import CollatzLean.Collatz2.ObstructionAudit.MainModel

/-!
# Collatz2 Obstruction Audit: exact word-realizability mismatch

主 model は `oddCoeff = 3^p`, `twoCoeff = 2^H` と
prepend-one exponent profile まで genuine word と一致する。

しかし `AffineTransfer.ofWord` は diagonal だけでなく
`translate = Word.affineConst word` まで固定するため、主 model は exact affine
transfer として genuine word ではない。

注意: これはもはや「exact translation が最初の失敗境界」という主張ではない。
`TranslationShadowAudit` により、exact equality より薄い endpoint-side congruence や
path-size shadow の段階ですでに synthetic witness を分離できることが分かっている。
このファイルは exact mismatch 自体を regression fact として保持する。
-/

namespace Collatz2
namespace ObstructionAudit
namespace MainModel

/-- `[1,3]` の genuine affine constant は5。 -/
theorem auditWord_affineConst :
    Word.affineConst ([1, 3] : Word) = 5 := by
  norm_num [Word.affineConst]

/-- 主 model の translation は genuine `[1,3]` translation と一致しない。 -/
theorem translate_ne_auditWord_affineConst (n : ℕ) :
    translate n ≠ Word.affineConst (word n) := by
  simp [translate, word, Word.affineConst]

/--
主 model は diagonal では `[1,3]` と一致するが、
exact affine transfer としては `ofWord [1,3]` ではない。
-/
theorem transfer_ne_ofWord (n : ℕ) :
    transfer n ≠ AffineTransfer.ofWord (word n) := by
  intro h
  have ht := congrArg AffineTransfer.translate h
  exact (translate_ne_auditWord_affineConst n) (by
    simpa [transfer, AffineTransfer.ofWord] using ht)

/--
主 model が通過する old-style boundary:
primitive-center / return-gap / positive-kappa / `3^p,2^H` diagonal /
prepend-one profile までは同時に成立するが、exact word translation は成立しない。
-/
theorem diagonal_profile_without_word_translation_is_satisfiable :
    Nonempty DiagonalWordProfileConstraints :=
  constraints_satisfiable

end MainModel
end ObstructionAudit
end Collatz2
