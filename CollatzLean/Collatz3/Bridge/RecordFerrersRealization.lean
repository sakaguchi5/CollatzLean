import CollatzLean.Collatz3.Canonical.OddEndpointResidue
import CollatzLean.Collatz3.Critical.ProfileCanonical
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Ferrers.RecordFerrers

/-!
# Collatz3 Bridge: RecordFerrers packet と初期値 residue

このファイルでは `canonicalRecordLengths` から exponent word を逆復元する定義を置かない。
現行の `canonicalRecordLengths` は profile から決まる deterministic partition の派生 view であり、
length 列だけを full word の符号化として扱う根拠はまだないためである。

代わりに、同じ finite Collatz packet を

* word 側: `w`, `affineConst w`, `Word.oddStartClass w`,
* profile / RecordFerrers 側: `profileFromWord w`, `canonicalRecordLengths`,
  `profileAffineNumerator`, `profileOddStartClass`,

という二つの view で読む。

保存する新しい数学データはない。
`IsWordRecordRealization` は RecordFerrers の underlying profile が
`profileFromWord w` と同じである、という最小の関係だけを持つ。
初期値 residue の正本は既存 `profileOddStartClass` / `Word.oddStartClass` をそのまま使う。
-/

namespace Collatz3
namespace Bridge

/--
word と RecordFerrers が同じ finite critical profile を表すこと。

word や record lengths を structure field として重複保存せず、
underlying profile の equality だけを packet compatibility とする。
-/
def IsWordRecordRealization
    {w : Word}
    (R : Ferrers.RecordFerrers (Word.oddSteps w)) : Prop :=
  R.profile.1 = Critical.profileFromWord w

/--
RecordFerrers packet が指定する odd-start residue class。

新しい residue 計算は導入せず、underlying profile の既存正本をそのまま公開する薄い alias。
-/
abbrev recordRealizationClass
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    ZMod (Critical.profileOddEndpointModulus m) :=
  Critical.profileOddStartClass R.profile.1

/--
RecordFerrers packet が指定する residue class の最小非負代表。
-/
abbrev recordCanonicalInitialValue
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) : ℕ :=
  Critical.profileCanonicalStart R.profile.1

@[simp] theorem recordCanonicalInitialValue_eq_class_val
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    recordCanonicalInitialValue R =
      (recordRealizationClass R).val := by
  exact Critical.profileCanonicalStart_eq_oddStartClass_val R.profile.1

namespace IsWordRecordRealization

/--
同じ packet なら RecordFerrers 側の canonical length 列は、
word から抽出した profile の deterministic length 列そのもの。

これは lengths から word を復元する主張ではなく、同じ profile の二つの view の一致である。
-/
theorem canonicalRecordLengths_eq
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (h : IsWordRecordRealization R) :
    Ferrers.canonicalRecordLengths R.profile.1 =
      Ferrers.canonicalRecordLengths (Critical.profileFromWord w) := by
  unfold IsWordRecordRealization at h
  rw [h]

/--
critical first-passage word と同じ RecordFerrers packet では、
profile affine numerator は word の `affineConst` に exact に一致する。
-/
theorem profileAffineNumerator_eq_affineConst
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (h : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    Critical.profileAffineNumerator R.profile.1 =
      Word.affineConst w := by
  unfold IsWordRecordRealization at h
  rw [h]
  exact
    Critical.profileAffineNumerator_profileFromWord_eq_affineConst hFirst

/--
critical first-passage word と同じ packet では、profile 側と word 側で
odd endpoint を分類する modulus が一致する。
-/
theorem oddEndpointModulus_eq_word
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (_h : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    Critical.profileOddEndpointModulus (Word.oddSteps w) =
      Word.oddEndpointModulus w := by
  rw [Critical.profileOddEndpointModulus_eq,
    Word.oddEndpointModulus_eq, hFirst.totalTwoDepth_eq]

/--
同じ packet の canonical initial value は、word affine data が指定する
canonical start と exact に一致する。

従って RecordFerrers/profile から得る residue representative と
word から得る residue representative は別データではない。
-/
theorem canonicalInitialValue_eq_wordCanonicalStart
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (h : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    recordCanonicalInitialValue R = Word.canonicalStart w := by
  unfold IsWordRecordRealization at h
  unfold recordCanonicalInitialValue
  rw [h]
  unfold Critical.profileCanonicalStart Word.canonicalStart
  rw [← hFirst.totalTwoDepth_eq]
  rw [Critical.profileAffineNumerator_profileFromWord_eq_affineConst hFirst]

/--
同じ finite packet から読んだ三つの派生 view をまとめた theorem。

* canonical record lengths,
* affine numerator,
* canonical initial value

はいずれも同じ word/profile から導かれ、独立な packet field ではない。
-/
theorem derivedViews
    {w : Word}
    {R : Ferrers.RecordFerrers (Word.oddSteps w)}
    (h : IsWordRecordRealization R)
    (hFirst : Word.CriticalFirstPassage w) :
    Ferrers.canonicalRecordLengths R.profile.1 =
        Ferrers.canonicalRecordLengths (Critical.profileFromWord w) ∧
      Critical.profileAffineNumerator R.profile.1 = Word.affineConst w ∧
      recordCanonicalInitialValue R = Word.canonicalStart w := by
  exact ⟨h.canonicalRecordLengths_eq,
    h.profileAffineNumerator_eq_affineConst hFirst,
    h.canonicalInitialValue_eq_wordCanonicalStart hFirst⟩

end IsWordRecordRealization

/--
actual odd endpoint を持つ同一 word の start は、
RecordFerrers packet が指定する profile residue class に属する。

これが

`RecordFerrers/profile packet -> initial-value residue mod 2^(H+1)`

という realization map の exact correctness theorem。
residue の数学的正本は既存 `profileOddStartClass` であり、ここでは重複定義しない。
-/
theorem endpoint_start_has_recordRealizationClass
    {w : Word}
    (hFirst : Word.CriticalFirstPassage w)
    (R : Ferrers.RecordFerrers (Word.oddSteps w))
    (hReal : IsWordRecordRealization R)
    {x y : ℕ}
    (hEndpoint : w.EndpointEquation x y)
    (hy : Odd y) :
    ((x : ℕ) :
        ZMod (Critical.profileOddEndpointModulus (Word.oddSteps w))) =
      recordRealizationClass R := by
  have hw := hEndpoint.start_has_oddStartClass hy
  unfold IsWordRecordRealization at hReal
  unfold recordRealizationClass
  unfold Critical.profileOddEndpointModulus
    Critical.profileOddStartClass
  unfold Word.oddEndpointModulus Word.oddStartClass at hw
  rw [← hFirst.totalTwoDepth_eq]
  rw [hReal]
  rw [Critical.profileAffineNumerator_profileFromWord_eq_affineConst hFirst]
  exact hw

end Bridge
end Collatz3
