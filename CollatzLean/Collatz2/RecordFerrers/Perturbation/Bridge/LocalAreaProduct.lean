import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.FixedSkeletonDecorationEquivalence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationAreaDecomposition

/-!
# Record–Ferrers Perturbation / Local Area Product

`FixedSkeletonDecorationEquivalence` までで、primitive + StripReduced fixed chord 上の
fixed-skeleton actual state space は

  FixedSkeletonSource P u D
    ≃ LocalDecorationTuple D.lengths

と exact に同一視された。

一方 `LocalDecorationAreaDecomposition` では、一つの valid local word `w` に対して

  localDecorationArea w
    = affineConst w - baseAffineConst (oddSteps w)

を定義し、これが local fixed fiber の Ferrers weighted area そのものであること、
さらに global decoration residual がこれら local areas の skeleton-weighted sumであることを
証明した。

本ファイルではこの二つを合成する。

各 fixed length `r` について、実際に genuine `LocalDecoration r` から実現される area 値だけを

  LocalAreaValue r

とし、

  LocalDecoration r ≃ LocalAreaValue r

を証明する。area が同じなら affine translation も同じであり、
fixed length の valid minimal block は `(length, affineConst)` から一意に復元できるため、
local area は一つの local decoration を lossless に決める。

これを length list 全体へ componentwise に持ち上げ、

  LocalDecorationTuple D.lengths
    ≃ LocalAreaTuple D.lengths

を得る。従って最終的に

  FixedSkeletonSource P u D
    ≃ LocalAreaTuple D.lengths

となる。

さらに `LocalAreaTuple.weightedArea` が既存
`recordLocalWeightedDecorationArea` と exact に一致することを示し、元 source について

  decorationGap
    = 2 * LocalAreaTuple.weightedArea

まで閉じる。

注意:
`LocalAreaValue r` は任意の `ℕ` ではなく、length `r` の genuine local decoration が
実際に実現する area spectrum である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 一つの local decoration の realizable area spectrum -/

/--
length `r` の genuine local decoration が実現する local Ferrers area 値。

任意の自然数ではなく、実現可能値だけを subtype として保持する。
-/
def LocalAreaValue (r : ℕ) : Type :=
  {A : ℕ //
    ∃ L : LocalDecoration r,
      localDecorationArea L.word = A}

namespace LocalAreaValue

/-- realizable area value が持つ witness decoration を一つ選ぶ。 -/
noncomputable def chooseDecoration
    {r : ℕ}
    (A : LocalAreaValue r) : LocalDecoration r :=
  Classical.choose A.property

/-- chosen decoration の local area は spectrum value そのもの。 -/
theorem chooseDecoration_area
    {r : ℕ}
    (A : LocalAreaValue r) :
    localDecorationArea A.chooseDecoration.word = A.1 :=
  Classical.choose_spec A.property

end LocalAreaValue

namespace LocalDecoration

/-- local decoration をその realizable area spectrum point へ送る。 -/
def toAreaValue
    {r : ℕ}
    (L : LocalDecoration r) : LocalAreaValue r :=
  ⟨localDecorationArea L.word, ⟨L, rfl⟩⟩

@[simp] theorem toAreaValue_val
    {r : ℕ}
    (L : LocalDecoration r) :
    L.toAreaValue.1 = localDecorationArea L.word := rfl

/--
同じ fixed length の二つの genuine local decorations は、
local decoration area が等しければ同一。

area equality
→ `affineConst = baseAffineConst r + area` equality
→ fixed-length valid-minimal uniqueness
という流れ。
-/
theorem eq_of_localDecorationArea_eq
    {r : ℕ}
    {A B : LocalDecoration r}
    (hArea :
      localDecorationArea A.word =
        localDecorationArea B.word) :
    A = B := by
  apply LocalDecoration.ext
  apply validMinimalBlock_unique_of_same_length_affineConst
    A.validMinimal B.validMinimal
  · exact A.length_eq.trans B.length_eq.symm
  · have hA :=
      affineConst_eq_baseAffineConst_add_localDecorationArea
        A.word A.validMinimal.valid
    have hB :=
      affineConst_eq_baseAffineConst_add_localDecorationArea
        B.word B.validMinimal.valid
    rw [A.length_eq] at hA
    rw [B.length_eq] at hB
    calc
      affineConst A.word
          = baseAffineConst r + localDecorationArea A.word := hA
      _ = baseAffineConst r + localDecorationArea B.word := by
            rw [hArea]
      _ = affineConst B.word := hB.symm

/--
## Local Area Coordinate Equivalence

fixed length `r` の genuine local decoration は、その realizable local area 値だけで
lossless に符号化される。
-/
noncomputable def equivAreaValue
    (r : ℕ) :
    LocalDecoration r ≃ LocalAreaValue r where
  toFun := fun L => L.toAreaValue
  invFun := fun A => A.chooseDecoration
  left_inv := by
    intro L
    apply eq_of_localDecorationArea_eq
    have h := (L.toAreaValue).chooseDecoration_area
    simpa using h
  right_inv := by
    intro A
    apply Subtype.ext
    change localDecorationArea A.chooseDecoration.word = A.1
    exact A.chooseDecoration_area

@[simp] theorem chooseDecoration_toAreaValue
    {r : ℕ}
    (L : LocalDecoration r) :
    L.toAreaValue.chooseDecoration = L :=
  (equivAreaValue r).left_inv L

end LocalDecoration

namespace LocalAreaValue

@[simp] theorem toAreaValue_chooseDecoration
    {r : ℕ}
    (A : LocalAreaValue r) :
    A.chooseDecoration.toAreaValue = A :=
  (LocalDecoration.equivAreaValue r).right_inv A

end LocalAreaValue

/-! ## 2. length list 上の dependent local-area product -/

/--
length list `[r₁,...,rₘ]` の各成分に、その length で実現可能な `LocalAreaValue` を一つずつ
載せた dependent product。

概念的には

  LocalAreaValue r₁ × ... × LocalAreaValue rₘ

である。
-/
inductive LocalAreaTuple : List ℕ → Type
  | nil : LocalAreaTuple []
  | cons {r : ℕ} {rs : List ℕ} :
      LocalAreaValue r →
      LocalAreaTuple rs →
      LocalAreaTuple (r :: rs)

namespace LocalAreaTuple

/-- area tuple の underlying natural-number area vector。 -/
def values {rs : List ℕ} (A : LocalAreaTuple rs) : List ℕ :=
  match A with
  | .nil => []
  | .cons a as => a.1 :: values as

@[simp] theorem values_nil :
    values LocalAreaTuple.nil = [] := rfl

@[simp] theorem values_cons
    {r : ℕ}
    {rs : List ℕ}
    (a : LocalAreaValue r)
    (as : LocalAreaTuple rs) :
    values (LocalAreaTuple.cons a as) =
      a.1 :: values as := rfl

/-- area vector の長さは skeleton length list の長さと一致する。 -/
@[simp] theorem values_length
    {rs : List ℕ}
    (A : LocalAreaTuple rs) :
    A.values.length = rs.length := by
  induction A with
  | nil => rfl
  | cons a as ih =>
      simp [values, ih]

/-- area tuple を componentwise に local decoration tuple へ復号する。 -/
noncomputable def toLocalDecorationTuple
    {rs : List ℕ}
    (A : LocalAreaTuple rs) :
    LocalDecorationTuple rs :=
  match A with
  | .nil => .nil
  | .cons a as =>
      .cons a.chooseDecoration as.toLocalDecorationTuple

end LocalAreaTuple

namespace LocalDecorationTuple

/-- local decoration tuple を componentwise に realizable area tuple へ送る。 -/
def toLocalAreaTuple
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    LocalAreaTuple rs :=
  match T with
  | .nil => .nil
  | .cons L T =>
      .cons L.toAreaValue T.toLocalAreaTuple

/-- componentwise area encoding の underlying vector は block ごとの `localDecorationArea` 列。 -/
@[simp] theorem toLocalAreaTuple_values
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    T.toLocalAreaTuple.values =
      T.blocks.map localDecorationArea := by
  induction T with
  | nil =>
      rfl
  | @cons r rs L T ih =>
      simp [toLocalAreaTuple,  blocks, ih]

/-- decoration tuple → area tuple → decoration tuple は exact identity。 -/
@[simp] theorem toLocalAreaTuple_toLocalDecorationTuple
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    T.toLocalAreaTuple.toLocalDecorationTuple = T := by
  induction T with
  | nil =>
      rfl
  | @cons r rs L T ih =>
      simp [toLocalAreaTuple,
        LocalAreaTuple.toLocalDecorationTuple, ih]

end LocalDecorationTuple

namespace LocalAreaTuple

/-- area tuple → decoration tuple → area tuple は exact identity。 -/
@[simp] theorem toLocalDecorationTuple_toLocalAreaTuple
    {rs : List ℕ}
    (A : LocalAreaTuple rs) :
    A.toLocalDecorationTuple.toLocalAreaTuple = A := by
  induction A with
  | nil =>
      rfl
  | @cons r rs a as ih =>
      simp [toLocalDecorationTuple,
        LocalDecorationTuple.toLocalAreaTuple, ih]

end LocalAreaTuple

/--
## Local Decoration Product ≃ Local Area Product

length list 全体について、local decoration dependent product は componentwise realizable
local-area dependent product と exact に同値。
-/
noncomputable def localDecorationTupleEquivAreaTuple
    (rs : List ℕ) :
    LocalDecorationTuple rs ≃ LocalAreaTuple rs where
  toFun := fun T => T.toLocalAreaTuple
  invFun := fun A => A.toLocalDecorationTuple
  left_inv := LocalDecorationTuple.toLocalAreaTuple_toLocalDecorationTuple
  right_inv := LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple

/-! ## 3. fixed-skeleton actual source space の area-product equivalence -/

/--
## Local Area Product 主定理

primitive + StripReduced fixed chord 上で、fixed-skeleton actual source space は
各 record block length の realizable local-area spectrum の dependent product と exact に同値。

  FixedSkeletonSource P u D
    ≃ LocalAreaTuple D.lengths
-/
noncomputable def fixedSkeletonSourceEquivLocalAreaProduct
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonSource P u D ≃
      LocalAreaTuple D.lengths :=
  (fixedSkeletonSourceEquiv
      P hPrimitive hReduced u D).trans
    (localDecorationTupleEquivAreaTuple D.lengths)

/-- fixed-skeleton actual source の canonical local-area product coordinate。 -/
noncomputable def fixedSkeletonLocalAreaTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    LocalAreaTuple D.lengths :=
  (fixedSkeletonSourceEquivLocalAreaProduct
    P hPrimitive hReduced u D) X

/-- area-product coordinate は extracted local decoration tuple の componentwise area encoding。 -/
theorem fixedSkeletonLocalAreaTuple_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X =
      X.toLocalDecorationTuple.toLocalAreaTuple := by
  rfl

/-- area-product coordinates が同じ fixed-skeleton sources は同一。 -/
theorem fixedSkeletonSource_eq_of_same_localAreaTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {X Y : FixedSkeletonSource P u D}
    (hArea :
      fixedSkeletonLocalAreaTuple
          P hPrimitive hReduced u D X =
        fixedSkeletonLocalAreaTuple
          P hPrimitive hReduced u D Y) :
    X = Y := by
  exact
    (fixedSkeletonSourceEquivLocalAreaProduct
      P hPrimitive hReduced u D).injective hArea

/-- 任意 realizable local-area tuple は unique な fixed-skeleton actual source を与える。 -/
theorem exists_unique_fixedSkeletonSource_of_localAreaTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (A : LocalAreaTuple D.lengths) :
    ∃! X : FixedSkeletonSource P u D,
      fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X = A := by
  let e :=
    fixedSkeletonSourceEquivLocalAreaProduct
      P hPrimitive hReduced u D
  refine ⟨e.symm A, ?_, ?_⟩
  · exact e.apply_symm_apply A
  · intro X hX
    exact e.injective (hX.trans (e.apply_symm_apply A).symm)

/-! ## 4. product area evaluator -/

namespace LocalAreaTuple

/--
skeleton affine weights で local area vector を集約する product potential。

既存 `weightedLocalDecorationArea` と同じ evaluator を area-product coordinate に適用する。
-/
def weightedArea
    {rs : List ℕ}
    (A : LocalAreaTuple rs) : ℕ :=
  weightedLocalDecorationArea rs A.values

end LocalAreaTuple

/-- fixed-skeleton source の area tuple values は chosen decomposition の local area vector そのもの。 -/
theorem fixedSkeletonLocalAreaTuple_values_eq_localDecorationAreas
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X).values =
      localDecorationAreas X.decomposition := by
  rw [fixedSkeletonLocalAreaTuple_eq]
  calc
    X.toLocalDecorationTuple.toLocalAreaTuple.values
        = X.toLocalDecorationTuple.blocks.map localDecorationArea :=
          X.toLocalDecorationTuple.toLocalAreaTuple_values
    _ = X.decomposition.blocks.map localDecorationArea := by
          rw [X.toLocalDecorationTuple_blocks]
    _ = localDecorationAreas X.decomposition := rfl

/--
## Product Potential Identification

fixed-skeleton source の product-coordinate weighted area は、chosen genuine
RecordDecomposition の `recordLocalWeightedDecorationArea` と exact に一致する。
-/
theorem fixedSkeletonLocalAreaTuple_weightedArea_eq_recordLocalWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X).weightedArea =
      recordLocalWeightedDecorationArea X.decomposition := by
  unfold LocalAreaTuple.weightedArea
  unfold recordLocalWeightedDecorationArea
  rw [
    fixedSkeletonLocalAreaTuple_values_eq_localDecorationAreas
      P hPrimitive hReduced u D X
  ]
  rw [X.decomposition_lengths]

/-- same source の別 decomposition を選んでも product weighted area は同じ。 -/
theorem fixedSkeletonLocalAreaTuple_weightedArea_eq_any_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D)
    (E : RecordDecomposition X.1 1)
    (hLengths : E.lengths = D.lengths) :
    (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X).weightedArea =
      recordLocalWeightedDecorationArea E := by
  calc
    (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X).weightedArea
        = recordLocalWeightedDecorationArea X.decomposition :=
          fixedSkeletonLocalAreaTuple_weightedArea_eq_recordLocalWeightedDecorationArea
            P hPrimitive hReduced u D X
    _ = recordLocalWeightedDecorationArea E := by
      unfold recordLocalWeightedDecorationArea localDecorationAreas
      rw [X.decomposition_lengths, hLengths]
      rw [X.decomposition.blocks_unique E]

/-! ## 5. 元 source の product coordinate と既存 decorationGap の同定 -/

/-- 元 source `u` 自身を fixed-skeleton source space の点として見る。 -/
def sourceFixedSkeletonSource
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonSource P u D :=
  ⟨u, ⟨D, rfl⟩⟩

/-- 元 source の record local weighted area は area-product weighted coordinate そのもの。 -/
theorem recordLocalWeightedDecorationArea_eq_sourceAreaProductWeightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    recordLocalWeightedDecorationArea D =
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D
        (sourceFixedSkeletonSource P u D)).weightedArea := by
  symm
  have h :=
    fixedSkeletonLocalAreaTuple_weightedArea_eq_any_decomposition
      P hPrimitive hReduced u D
      (sourceFixedSkeletonSource P u D)
      D
      rfl
  exact h

/-- 既存 `localWeightedDecorationArea` も元 source の area-product potential そのもの。 -/
theorem localWeightedDecorationArea_eq_sourceAreaProductWeightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    localWeightedDecorationArea P u D =
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D
        (sourceFixedSkeletonSource P u D)).weightedArea := by
  unfold localWeightedDecorationArea
  exact
    recordLocalWeightedDecorationArea_eq_sourceAreaProductWeightedArea
      P hPrimitive hReduced u D

/--
## Arithmetic出口

元 source の `decorationGap` は area-product coordinate の weighted potential の
exact 2 倍。
-/
theorem decorationGap_eq_two_mul_sourceAreaProductWeightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    decorationGap P hPrimitive hReduced u D =
      2 *
        (fixedSkeletonLocalAreaTuple
          P hPrimitive hReduced u D
          (sourceFixedSkeletonSource P u D)).weightedArea := by
  rw [
    decorationGap_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D
  ]
  rw [
    localWeightedDecorationArea_eq_sourceAreaProductWeightedArea
      P hPrimitive hReduced u D
  ]

/-! ## 6. closure package -/

/--
Local Area Product 層で閉じた内容。

* fixed-skeleton actual state space と local-area product の exact equivalence
* product weighted area と record local weighted area の exact identification
* source decoration gap の product-potential formula
-/
structure LocalAreaProductClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  area_product_bijective :
    Function.Bijective
      (fun X : FixedSkeletonSource P u D =>
        fixedSkeletonLocalAreaTuple
          P hPrimitive hReduced u D X)
  source_weighted_area_formula :
    localWeightedDecorationArea P u D =
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D
        (sourceFixedSkeletonSource P u D)).weightedArea
  source_decoration_gap_formula :
    decorationGap P hPrimitive hReduced u D =
      2 *
        (fixedSkeletonLocalAreaTuple
          P hPrimitive hReduced u D
          (sourceFixedSkeletonSource P u D)).weightedArea

/-- Local Area Product closure theorem。 -/
theorem localAreaProduct_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    LocalAreaProductClosed
      P hPrimitive hReduced u D := by
  let e :=
    fixedSkeletonSourceEquivLocalAreaProduct
      P hPrimitive hReduced u D
  exact {
    area_product_bijective := e.bijective
    source_weighted_area_formula :=
      localWeightedDecorationArea_eq_sourceAreaProductWeightedArea
        P hPrimitive hReduced u D
    source_decoration_gap_formula :=
      decorationGap_eq_two_mul_sourceAreaProductWeightedArea
        P hPrimitive hReduced u D
  }

end RecordFerrers
end Collatz2
