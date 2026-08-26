import CollatzLean.Collatz2.RecordFerrers.Lattice.UniversalFirstCrossingFiber
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.LocalTranslationSet

/-!
# Record–Ferrers RF-A+8: local translation coordinates

fixed length の valid minimal block は affine translation `B` 一個で一意に決まる。
この事実を explicit equivalence として package し、record decoration 全体を
`(block length, local B)` 列へ lossless に圧縮する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- length `r` の genuine local decoration。 -/
structure LocalDecoration (r : ℕ) where
  word : Word
  validMinimal : ValidMinimalBlock word
  length_eq : oddSteps word = r

namespace LocalDecoration

@[ext] theorem ext
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : A.word = B.word) :
    A = B := by
  cases A
  cases B
  simp_all

/-- local decoration の exact affine translation。 -/
def translation
    {r : ℕ}
    (D : LocalDecoration r) : ℕ :=
  affineConst D.word

/-- local decoration の translation は local spectrum に属する。 -/
theorem translation_mem
    {r : ℕ}
    (D : LocalDecoration r) :
    D.translation ∈ localTranslationSet r := by
  exact ⟨D.word, D.validMinimal, D.length_eq, rfl⟩

end LocalDecoration

/-- length `r` の local translation spectrum を subtype として読む。 -/
abbrev LocalTranslationValue (r : ℕ) :=
  {B : ℕ // B ∈ localTranslationSet r}

namespace LocalTranslationValue

/-- spectrum point が保持する witness word。 -/
noncomputable def chooseWord
    {r : ℕ}
    (V : LocalTranslationValue r) : Word :=
  Classical.choose V.property

/-- chosen witness は valid minimal block。 -/
theorem chooseWord_validMinimal
    {r : ℕ}
    (V : LocalTranslationValue r) :
    ValidMinimalBlock V.chooseWord :=
  (Classical.choose_spec V.property).1

/-- chosen witness の odd length は指定 length。 -/
theorem chooseWord_oddSteps
    {r : ℕ}
    (V : LocalTranslationValue r) :
    oddSteps V.chooseWord = r :=
  (Classical.choose_spec V.property).2.1

/-- chosen witness の affine translation は spectrum value そのもの。 -/
theorem chooseWord_affineConst
    {r : ℕ}
    (V : LocalTranslationValue r) :
    affineConst V.chooseWord = V.1 :=
  (Classical.choose_spec V.property).2.2

/-- spectrum value から canonical local decoration を復号する。 -/
noncomputable def toLocalDecoration
    {r : ℕ}
    (V : LocalTranslationValue r) : LocalDecoration r :=
  { word := V.chooseWord
    validMinimal := V.chooseWord_validMinimal
    length_eq := V.chooseWord_oddSteps }

end LocalTranslationValue

namespace LocalDecoration

/-- local decoration を spectrum value へ encode。 -/
def toTranslationValue
    {r : ℕ}
    (D : LocalDecoration r) : LocalTranslationValue r :=
  ⟨D.translation, D.translation_mem⟩

/--
fixed length の local decoration と local translation spectrum は exact に同値。
-/
noncomputable def equivTranslationValue
    (r : ℕ) :
    LocalDecoration r ≃ LocalTranslationValue r where
  toFun := fun D => D.toTranslationValue
  invFun := fun V => V.toLocalDecoration
  left_inv := by
    intro D
    apply LocalDecoration.ext
    apply validMinimalBlock_unique_of_same_length_affineConst
      (LocalTranslationValue.toLocalDecoration D.toTranslationValue).validMinimal
      D.validMinimal
    · exact
        (LocalTranslationValue.toLocalDecoration D.toTranslationValue).length_eq.trans
          D.length_eq.symm
    · have hChoose :=
        (D.toTranslationValue).chooseWord_affineConst
      simpa [LocalTranslationValue.toLocalDecoration,
        toTranslationValue, translation] using hChoose
  right_inv := by
    intro V
    apply Subtype.ext
    have hChoose := V.chooseWord_affineConst
    simpa [toTranslationValue, translation,
      LocalTranslationValue.toLocalDecoration] using hChoose

end LocalDecoration

/-- one local block の compressed coordinate `(length, B)`。 -/
def blockTranslationCoordinate (w : Word) : ℕ × ℕ :=
  (oddSteps w, affineConst w)

/-- valid minimal block lists は `(length,B)` coordinate list から一意に復元できる。 -/
theorem validMinimalBlocks_eq_of_coordinateMap_eq
    {as bs : List Word}
    (hA : ∀ a ∈ as, ValidMinimalBlock a)
    (hB : ∀ b ∈ bs, ValidMinimalBlock b)
    (hCoord :
      as.map blockTranslationCoordinate =
        bs.map blockTranslationCoordinate) :
    as = bs := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          simp [blockTranslationCoordinate] at hCoord
  | cons a as ih =>
      cases bs with
      | nil =>
          simp [blockTranslationCoordinate] at hCoord
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at hCoord
          have hPair := hCoord.1
          have hLen : oddSteps a = oddSteps b := by
            exact congrArg Prod.fst hPair
          have hAffine : affineConst a = affineConst b := by
            exact congrArg Prod.snd hPair
          have ha : ValidMinimalBlock a := hA a (by simp)
          have hb : ValidMinimalBlock b := hB b (by simp)
          have hab : a = b :=
            validMinimalBlock_unique_of_same_length_affineConst
              ha hb hLen hAffine
          subst b
          have hATail : ∀ c ∈ as, ValidMinimalBlock c := by
            intro c hc
            exact hA c (by simp [hc])
          have hBTail : ∀ c ∈ bs, ValidMinimalBlock c := by
            intro c hc
            exact hB c (by simp [hc])
          have hTail : as = bs := ih hATail hBTail hCoord.2
          rw [hTail]

namespace ValidDecoratedSkeleton

/-- decoration 全体の `(length, local B)` coordinate list。 -/
def translationCoordinates
    {S : Skeleton}
    (D : ValidDecoratedSkeleton S) : List (ℕ × ℕ) :=
  D.blocks.map blockTranslationCoordinate

/-- coordinate の first components は skeleton lengths と exact に一致。 -/
theorem translationCoordinates_lengths
    {S : Skeleton}
    (D : ValidDecoratedSkeleton S) :
    D.translationCoordinates.map Prod.fst = S.lengths := by
  unfold translationCoordinates
  rw [List.map_map]
  change D.blocks.map oddSteps = S.lengths
  exact D.lengths_eq

/-- coordinate の second component は各 local block の affine translation。 -/
theorem translationCoordinates_translations
    {S : Skeleton}
    (D : ValidDecoratedSkeleton S) :
    D.translationCoordinates.map Prod.snd =
      D.blocks.map affineConst := by
  unfold translationCoordinates blockTranslationCoordinate
  rw [List.map_map]
  rfl

/--
同じ skeleton 上の valid decoration は `(length,B)` coordinate list だけで lossless。
-/
theorem blocks_eq_of_translationCoordinates_eq
    {S : Skeleton}
    (A B : ValidDecoratedSkeleton S)
    (hCoord : A.translationCoordinates = B.translationCoordinates) :
    A.blocks = B.blocks := by
  apply validMinimalBlocks_eq_of_coordinateMap_eq
  · intro a ha
    exact {
      toMinimalBlock := A.minimal a ha
      valid := A.valid a ha
    }
  · intro b hb
    exact {
      toMinimalBlock := B.minimal b hb
      valid := B.valid b hb
    }
  · exact hCoord

/-- coordinate equality は ValidDecoratedSkeleton 自体の equality を強制する。 -/
theorem eq_of_translationCoordinates_eq
    {S : Skeleton}
    (A B : ValidDecoratedSkeleton S)
    (hCoord : A.translationCoordinates = B.translationCoordinates) :
    A = B := by
  have hBlocks := A.blocks_eq_of_translationCoordinates_eq B hCoord
  cases A with
  | mk DA hValidA =>
      cases B with
      | mk DB hValidB =>
          cases DA with
          | mk blocksA hLenA hMinA =>
              cases DB with
              | mk blocksB hLenB hMinB =>
                  dsimp at hBlocks
                  subst blocksB
                  rfl

end ValidDecoratedSkeleton

namespace RecordDecomposition

/-- genuine record decomposition の lossless local translation coordinates。 -/
def translationCoordinates
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) : List (ℕ × ℕ) :=
  D.toValidDecoratedSkeleton.translationCoordinates

/-- decomposition coordinate の length projection は canonical record skeleton。 -/
theorem translationCoordinates_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.translationCoordinates.map Prod.fst = D.lengths := by
  simpa [translationCoordinates] using
    D.toValidDecoratedSkeleton.translationCoordinates_lengths

/-- 同じ `x,start` の decompositions は local translation coordinates も一致する。 -/
theorem translationCoordinates_unique
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (A B : RecordDecomposition x start) :
    A.translationCoordinates = B.translationCoordinates := by
  have hBlocks := A.blocks_unique B
  unfold translationCoordinates ValidDecoratedSkeleton.translationCoordinates
  change
    A.blocks.map blockTranslationCoordinate =
      B.blocks.map blockTranslationCoordinate
  rw [hBlocks]

end RecordDecomposition

end RecordFerrers
end Collatz2
