import CollatzLean.Collatz3.CSTMicro.RoofEnvelope
import CollatzLean.Collatz3.Critical.ProfileExtraction

/-!
# Collatz3 CSTMicro: standard first-passage path から critical profile への canonical extraction

Stage 2B で standard parity first-passage と odd-only critical exponent word が
同じ first-crossing geometry の二つの座標表示であることを得た。

ここでは positive odd-count の path `P` に対して、existential witness を残さず

  P.word
    -> compressedExponentWord P
    -> extractedCriticalProfile P

という canonical な写像を定める。

その上で

* compressed word は valid,
* compressed word は `Word.CriticalFirstPassage`,
* standard length / odd count / affine numerator は保存される,
* 抽出 profile は `Critical.Admissible`,
* profile checkpoint は compressed word の prefix two-depth と exact に一致する,
* profile affine numerator は元の standard parity affine numerator と exact に一致する,

ことをすべて theorem として導く。

`endpointOddCount = 0` は odd-only exponent word を持たない trivial even crossing なので、
この bridge の本体からは意図的に分離する。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/--
standard parity word を Stage 2B の canonical compression で odd-only exponent word にする。

定義自体は全 path に置けるが、first-passage geometry を保存する theorem では
`0 < endpointOddCount` を仮定する。
-/
def compressedExponentWord (P : FirstPassagePath) : Word :=
  compressWord P.word

/--
canonical compressed exponent word から得る critical profile。
新しい profile 正本を作るのではなく、既存 `Critical.profileFromWord` の derived view とする。
-/
def extractedCriticalProfile (P : FirstPassagePath) :
    Critical.Profile (Word.oddSteps P.compressedExponentWord) :=
  Critical.profileFromWord P.compressedExponentWord

/-- positive odd-count path の canonical compressed word は valid。 -/
theorem compressedExponentWord_valid
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.Valid P.compressedExponentWord := by
  rcases P.exists_tail_of_endpointOddCount_pos hp with ⟨v, hWord⟩
  unfold compressedExponentWord
  rw [hWord]
  exact compressWord_true_valid v

/--
positive odd-count path は canonical compression の再展開で exact に元の parity word へ戻る。
-/
theorem expandWord_compressedExponentWord
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    expandWord P.compressedExponentWord = P.word := by
  rcases P.exists_tail_of_endpointOddCount_pos hp with ⟨v, hWord⟩
  unfold compressedExponentWord
  rw [hWord]
  exact expandWord_compressWord_true v

/-- positive odd-count path の canonical compressed word は critical first-passage。 -/
theorem compressedExponentWord_critical
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.CriticalFirstPassage P.compressedExponentWord := by
  exact
    criticalFirstPassage_of_expanded_firstPassage
      (P.compressedExponentWord_valid hp)
      P
      (P.expandWord_compressedExponentWord hp).symm

/-- canonical compressed word の odd-step 数は standard path の endpoint odd count と一致。 -/
theorem compressedExponentWord_oddSteps_eq
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.oddSteps P.compressedExponentWord = P.endpointOddCount := by
  calc
    Word.oddSteps P.compressedExponentWord
        = oddCount (expandWord P.compressedExponentWord) :=
          (oddCount_expandWord P.compressedExponentWord).symm
    _ = oddCount P.word := by
          rw [P.expandWord_compressedExponentWord hp]
    _ = P.endpointOddCount := rfl

/-- canonical compressed word の total two-depth は standard path length と一致。 -/
theorem compressedExponentWord_twoSteps_eq
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.twoSteps P.compressedExponentWord = P.length := by
  have hValid := P.compressedExponentWord_valid hp
  calc
    Word.twoSteps P.compressedExponentWord
        = (expandWord P.compressedExponentWord).length :=
          (length_expandWord_of_valid hValid).symm
    _ = P.word.length := by
          rw [P.expandWord_compressedExponentWord hp]
    _ = P.length := rfl

/--
canonical compressed word の odd-only affine translation は
元の standard parity affine numerator と exact に一致する。
-/
theorem compressedExponentWord_affineConst_eq
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.affineConst P.compressedExponentWord = affineConst P.word := by
  have hValid := P.compressedExponentWord_valid hp
  calc
    Word.affineConst P.compressedExponentWord
        = affineConst (expandWord P.compressedExponentWord) :=
          (affineConst_expandWord_eq_wordAffineConst hValid).symm
    _ = affineConst P.word := by
          rw [P.expandWord_compressedExponentWord hp]

/--
Stage 5 の三つの基本座標一致。

canonical compressed word は standard path と同じ `(p,H,B)` を持つ。
-/
theorem compressedExponentWord_sameStandardData
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.oddSteps P.compressedExponentWord = P.endpointOddCount ∧
      Word.twoSteps P.compressedExponentWord = P.length ∧
      Word.affineConst P.compressedExponentWord = affineConst P.word := by
  exact ⟨
    P.compressedExponentWord_oddSteps_eq hp,
    P.compressedExponentWord_twoSteps_eq hp,
    P.compressedExponentWord_affineConst_eq hp⟩

/-- positive odd-count path から canonical に抽出した critical profile は admissible。 -/
theorem extractedCriticalProfile_admissible
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.Admissible P.extractedCriticalProfile := by
  unfold extractedCriticalProfile
  exact
    Critical.profileFromWord_admissible
      (P.compressedExponentWord_critical hp)
      (P.compressedExponentWord_valid hp)

/--
抽出 profile の checkpoint は canonical compressed word の prefix two-depth に exact に戻る。
-/
theorem extractedCriticalProfile_checkpoint_eq_prefixTwoDepth
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (k : Fin (Word.oddSteps P.compressedExponentWord)) :
    Critical.checkpoint P.extractedCriticalProfile k =
      Word.prefixTwoDepth P.compressedExponentWord k.1 := by
  unfold extractedCriticalProfile
  exact
    Critical.checkpoint_profileFromWord_eq_prefixTwoDepth
      (P.compressedExponentWord_critical hp) k

/--
抽出 profile の affine numerator は元の standard parity affine numerator と exact に一致する。

これにより standard parity -> exponent word -> critical profile の変換で `B` は失われない。
-/
theorem extractedCriticalProfile_affineNumerator_eq
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.profileAffineNumerator P.extractedCriticalProfile =
      affineConst P.word := by
  calc
    Critical.profileAffineNumerator P.extractedCriticalProfile
        = Word.affineConst P.compressedExponentWord := by
            unfold extractedCriticalProfile
            exact
              Critical.profileAffineNumerator_profileFromWord_eq_affineConst
                (P.compressedExponentWord_critical hp)
    _ = affineConst P.word :=
          P.compressedExponentWord_affineConst_eq hp

/--
Stage 3 の Beatty-roof envelope は抽出 critical profile の affine numerator も抑える。
-/
theorem extractedCriticalProfile_affineNumerator_le_roofAffineBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.profileAffineNumerator P.extractedCriticalProfile ≤
      roofAffineBound P.endpointOddCount := by
  rw [P.extractedCriticalProfile_affineNumerator_eq hp]
  exact P.affineConst_le_roofAffineBound

/-- canonical compressed word の profile width は正。 -/
theorem compressedExponentWord_oddSteps_pos
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    0 < Word.oddSteps P.compressedExponentWord := by
  rw [P.compressedExponentWord_oddSteps_eq hp]
  exact hp

/--
存在形で使いたい後段のためのまとめ。

positive odd-count の任意の standard first-passage path は、
同じ parity word を展開として持つ valid critical exponent word と、
そこから canonical に得られる admissible critical profile を持つ。
さらに profile affine numerator は元の standard affine numeratorに一致する。
-/
theorem exists_admissibleCriticalProfile
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ∃ w : Word,
      Word.Valid w ∧
        Word.CriticalFirstPassage w ∧
        expandWord w = P.word ∧
        Critical.Admissible (Critical.profileFromWord w) ∧
        Critical.profileAffineNumerator (Critical.profileFromWord w) =
          affineConst P.word := by
  refine ⟨P.compressedExponentWord, ?_, ?_, ?_, ?_, ?_⟩
  · exact P.compressedExponentWord_valid hp
  · exact P.compressedExponentWord_critical hp
  · exact P.expandWord_compressedExponentWord hp
  · exact P.extractedCriticalProfile_admissible hp
  · exact P.extractedCriticalProfile_affineNumerator_eq hp

end FirstPassagePath
end CSTMicro
end Collatz3
