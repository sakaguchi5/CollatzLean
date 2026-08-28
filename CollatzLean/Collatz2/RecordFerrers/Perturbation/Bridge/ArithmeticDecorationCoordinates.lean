import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BooleanFamilyCanonicity
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates
import CollatzLean.Collatz2.Core.BlockAffineFactorization

/-!
# Record–Ferrers Perturbation / Arithmetic Decoration Coordinates

`ArithmeticDecorationCanonicity` では actual source から canonical flat top へ落とす際の
算術損失を一個の scalar `decorationGap` として canonical にした。

`BooleanFamilyCanonicity` では、その下にある Boolean / Ferrers / arithmetic deletion
system 全体が `RecordDecomposition` の選択に依存しないことを閉じた。

本ファイルでは、残っていた scalar `decorationGap` の「中身」を、既存の
`Reconstruction/TranslationCoordinates` に接続する。

既存理論では genuine record decomposition `D` の各 local block `b_i` は

  (oddSteps b_i, affineConst b_i)

という translation coordinate で lossless に符号化される。さらに fixed length の
valid minimal block は local `affineConst` 一個で一意に復元できる。

ここではこの coordinate list から global affine translation を exact に評価する
`coordinateWeightedTranslation` を定義し、

* source record suffix の `affineConst` を coordinate list だけから復元する。
* initial anchor prefix と合わせて source 全体の `affineConst` を exact に復元する。
* canonical flat top にも canonical record decomposition を一つ選び、その local
  translation coordinates を baseline として固定する。
* source coordinate evaluator と flat-top coordinate evaluator の差が exact に
  `decorationGap` であることを示す。
* actual source の fine arithmetic coordinate vector は Boolean boundary pattern を
  coarsen しても変えない。
* decomposition を変えても source coordinate vector / coordinate gap /
  decorated Boolean state は canonical transport の下で不変である。

従って Bridge の上段は

  actual source
      = canonical flat geometry
        + canonical fine local arithmetic coordinates

という lossless coordinate interpretation を持つ。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. `(length, local B)` coordinate list の weighted evaluator -/

/-- coordinate list が持つ total odd length。 -/
def coordinateOddSteps (cs : List (ℕ × ℕ)) : ℕ :=
  (cs.map Prod.fst).sum

/--
minimal block translation coordinates を global affine translation へ戻す evaluator。

`weightedBlockTranslation` の block formula

  3^(suffix odd length) * B_head
    + 2^(head minimal depth) * B_suffix

を coordinate data だけで再帰する。
-/
def coordinateWeightedTranslation : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (r, B) :: cs =>
      3 ^ coordinateOddSteps cs * B +
        2 ^ minimalDepth r * coordinateWeightedTranslation cs

/-- concrete block coordinate list の total odd length は flatten word の oddSteps。 -/
theorem coordinateOddSteps_map_blockTranslationCoordinate
    (bs : List Word) :
    coordinateOddSteps (bs.map blockTranslationCoordinate) =
      oddSteps bs.flatten := by
  rw [oddSteps_flatten_blocks]
  unfold coordinateOddSteps blockOddSteps blockTranslationCoordinate
  rw [List.map_map]
  rfl

/--
minimal block list を coordinate 化してから weighted evaluator に通すと、
core の `weightedBlockTranslation` と exact に一致する。
-/
theorem coordinateWeightedTranslation_map_blockTranslationCoordinate
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b) :
    coordinateWeightedTranslation (bs.map blockTranslationCoordinate) =
      weightedBlockTranslation bs := by
  revert hMinimal
  induction bs with
  | nil =>
      intro _
      rfl
  | cons b bs ih =>
      intro hMinimal
      have hb : MinimalBlock b := hMinimal b (by simp)
      have hTail : ∀ c ∈ bs, MinimalBlock c := by
        intro c hc
        exact hMinimal c (by simp [hc])
      have hTwo : twoSteps b = minimalDepth (oddSteps b) := by
        unfold minimalDepth
        exact hb.minimalDepth
      simp only [
        List.map_cons,
        coordinateWeightedTranslation,
        weightedBlockTranslation,
        blockTranslationCoordinate
      ]
      rw [
        coordinateOddSteps_map_blockTranslationCoordinate bs,
        ← hTwo,
        ih hTail
      ]

/-! ## 2. genuine RecordDecomposition coordinates の exact evaluator -/

/--
既存 `translationCoordinates` は定義通り block coordinate map そのもの。
後続の rewrite 用に公開 API として固定する。
-/
theorem RecordDecomposition.translationCoordinates_eq_blockCoordinateMap
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.translationCoordinates =
      D.blocks.map blockTranslationCoordinate := by
  unfold RecordDecomposition.translationCoordinates
  unfold ValidDecoratedSkeleton.translationCoordinates
  rfl

/-- decomposition coordinate list の total odd length は record suffix の oddSteps。 -/
theorem RecordDecomposition.coordinateOddSteps_translationCoordinates
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    coordinateOddSteps D.translationCoordinates =
      oddSteps D.blocks.flatten := by
  rw [D.translationCoordinates_eq_blockCoordinateMap]
  exact coordinateOddSteps_map_blockTranslationCoordinate D.blocks

/--
record local translation coordinates は suffix の genuine `affineConst` を exact に復元する。
-/
theorem RecordDecomposition.coordinateWeightedTranslation_eq_suffixAffineConst
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    coordinateWeightedTranslation D.translationCoordinates =
      affineConst D.blocks.flatten := by
  rw [D.translationCoordinates_eq_blockCoordinateMap]
  rw [coordinateWeightedTranslation_map_blockTranslationCoordinate
    D.blocks D.blocks_minimal]
  exact weightedBlockTranslation_eq_affineConst_flatten D.blocks

/--
record suffix が実際には `x.word.drop start` なので、coordinate evaluator は
その suffix affine translation そのもの。
-/
theorem RecordDecomposition.coordinateWeightedTranslation_eq_dropAffineConst
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    coordinateWeightedTranslation D.translationCoordinates =
      affineConst (x.word.drop start) := by
  rw [D.coordinateWeightedTranslation_eq_suffixAffineConst]
  rw [D.blocks_flatten_eq_drop]

/-- coordinate odd length も実 suffix oddSteps と exact に一致する。 -/
theorem RecordDecomposition.coordinateOddSteps_eq_dropOddSteps
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    coordinateOddSteps D.translationCoordinates =
      oddSteps (x.word.drop start) := by
  rw [D.coordinateOddSteps_translationCoordinates]
  rw [D.blocks_flatten_eq_drop]

/-! ## 3. anchor prefix と coordinate list から source 全体を復元 -/

/--
`start` より前の anchor prefix と、start 以後の local translation coordinates から
full word の affine translation を組み立てる。
-/
def sourceAffineFromCoordinates
    {p H : ℕ}
    (x : FiberPoint p H)
    {start : ℕ}
    (D : RecordDecomposition x start) : ℕ :=
  3 ^ coordinateOddSteps D.translationCoordinates *
      affineConst (x.word.take start) +
    2 ^ twoSteps (x.word.take start) *
      coordinateWeightedTranslation D.translationCoordinates

/--
source affine evaluator は genuine `affineConst x.word` を exact に復元する。

これは local coordinate theory と core `affineConst_append` の接続点。
-/
@[simp] theorem sourceAffineFromCoordinates_eq_source
    {p H : ℕ}
    (x : FiberPoint p H)
    {start : ℕ}
    (D : RecordDecomposition x start) :
    sourceAffineFromCoordinates x D = affineConst x.word := by
  unfold sourceAffineFromCoordinates
  rw [
    D.coordinateOddSteps_eq_dropOddSteps,
    D.coordinateWeightedTranslation_eq_dropAffineConst
  ]
  rw [← List.take_append_drop start x.word]
  rw [affineConst_append]
  simp only [List.take_append_drop]

/-! ## 4. actual source の fine arithmetic coordinate vector -/

/--
cut 1 genuine decomposition が持つ canonical fine arithmetic coordinates。

各成分は `(record block length, local affine translation)`。
-/
def arithmeticDecorationCoordinates
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : List (ℕ × ℕ) :=
  D.translationCoordinates

/-- coordinate の first projection は canonical record length skeleton。 -/
theorem arithmeticDecorationCoordinates_lengths
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    (arithmeticDecorationCoordinates D).map Prod.fst = D.lengths := by
  exact D.translationCoordinates_lengths

/-- coordinate の second projectionだけを local arithmetic translation vector と呼ぶ。 -/
def localArithmeticTranslations
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : List ℕ :=
  (arithmeticDecorationCoordinates D).map Prod.snd

/-- local arithmetic translation vector は block ごとの `affineConst` 列そのもの。 -/
theorem localArithmeticTranslations_eq_blockAffineConsts
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    localArithmeticTranslations D = D.blocks.map affineConst := by
  unfold localArithmeticTranslations arithmeticDecorationCoordinates
  rw [D.translationCoordinates_eq_blockCoordinateMap]
  rw [List.map_map]
  rfl

/--
actual source の fine coordinates は decomposition-independent。

これは既存 `RecordDecomposition.translationCoordinates_unique` の Bridge 解釈。
-/
theorem arithmeticDecorationCoordinates_independent_of_decomposition
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1) :
    arithmeticDecorationCoordinates D =
      arithmeticDecorationCoordinates E := by
  exact RecordDecomposition.translationCoordinates_unique D E

/-- second projection の local translation vector も decomposition-independent。 -/
theorem localArithmeticTranslations_independent_of_decomposition
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1) :
    localArithmeticTranslations D =
      localArithmeticTranslations E := by
  unfold localArithmeticTranslations
  rw [arithmeticDecorationCoordinates_independent_of_decomposition D E]

/-! ## 5. canonical flat top の local baseline coordinates -/

/--
全境界保持 canonical flat top は、その元 skeleton と同じ length list を持つ
record decomposition を持つ。
-/
theorem exists_canonicalFlatTopDecomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ∃ E : RecordDecomposition
        (canonicalFlatTop P hPrimitive hReduced u D) 1,
      E.lengths = D.lengths := by
  simpa [canonicalFlatTop, canonicalFlatPoint] using
    (exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D (retainAllBoundaries D))

/-- canonical flat top の baseline record decomposition を一つ選ぶ。 -/
noncomputable def canonicalFlatTopDecomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    RecordDecomposition
      (canonicalFlatTop P hPrimitive hReduced u D) 1 :=
  Classical.choose
    (exists_canonicalFlatTopDecomposition
      P hPrimitive hReduced u D)

/-- chosen flat-top decomposition は元の canonical length skeleton を exact に持つ。 -/
theorem canonicalFlatTopDecomposition_lengths
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (canonicalFlatTopDecomposition
      P hPrimitive hReduced u D).lengths = D.lengths :=
  Classical.choose_spec
    (exists_canonicalFlatTopDecomposition
      P hPrimitive hReduced u D)

/-- flat top の local baseline `(length,B)` coordinates。 -/
noncomputable def canonicalFlatTopCoordinates
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : List (ℕ × ℕ) :=
  (canonicalFlatTopDecomposition
    P hPrimitive hReduced u D).translationCoordinates

/-- flat-top baseline coordinates の length projection は source skeleton と一致。 -/
theorem canonicalFlatTopCoordinates_lengths
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (canonicalFlatTopCoordinates
      P hPrimitive hReduced u D).map Prod.fst = D.lengths := by
  unfold canonicalFlatTopCoordinates
  rw [RecordDecomposition.translationCoordinates_lengths]
  exact canonicalFlatTopDecomposition_lengths
    P hPrimitive hReduced u D

/-- source coordinates と flat baseline coordinates は同じ length skeleton 上にある。 -/
theorem arithmeticDecorationCoordinates_lengths_eq_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (arithmeticDecorationCoordinates D).map Prod.fst =
      (canonicalFlatTopCoordinates
        P hPrimitive hReduced u D).map Prod.fst := by
  rw [
    arithmeticDecorationCoordinates_lengths D,
    canonicalFlatTopCoordinates_lengths P hPrimitive hReduced u D
  ]

/--
flat-top decomposition の classical choice は coordinate level では無害。
同じ flat top の任意の genuine decomposition は同じ coordinates を持つ。
-/
theorem canonicalFlatTopCoordinates_eq_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition
      (canonicalFlatTop P hPrimitive hReduced u D) 1) :
    E.translationCoordinates =
      canonicalFlatTopCoordinates P hPrimitive hReduced u D := by
  unfold canonicalFlatTopCoordinates
  exact RecordDecomposition.translationCoordinates_unique
    E (canonicalFlatTopDecomposition P hPrimitive hReduced u D)

/-- flat-top coordinates から flat top の full affineConst を再構成する。 -/
noncomputable def flatTopAffineFromCoordinates
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  sourceAffineFromCoordinates
    (canonicalFlatTop P hPrimitive hReduced u D)
    (canonicalFlatTopDecomposition P hPrimitive hReduced u D)

/-- baseline coordinate evaluator は genuine flat-top `affineConst` に exact。 -/
@[simp] theorem flatTopAffineFromCoordinates_eq_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    flatTopAffineFromCoordinates P hPrimitive hReduced u D =
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word := by
  unfold flatTopAffineFromCoordinates
  exact sourceAffineFromCoordinates_eq_source
    (canonicalFlatTop P hPrimitive hReduced u D)
    (canonicalFlatTopDecomposition P hPrimitive hReduced u D)

/-! ## 6. scalar decorationGap を local coordinate difference として開く -/

/--
source coordinate evaluator と canonical flat baseline coordinate evaluator の差。

この scalar 自体は旧 `decorationGap` と一致するが、定義域側には
source / flat の local `(length,B)` coordinate systems が露出している。
-/
noncomputable def coordinateDecorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  sourceAffineFromCoordinates u D -
    flatTopAffineFromCoordinates P hPrimitive hReduced u D

/--
## 主定理 1: coordinate decoration gap = existing canonical decorationGap

従って従来の scalar residual は、local translation coordinates の weighted
reconstruction と canonical flat baseline の差として exact に読める。
-/
@[simp] theorem coordinateDecorationGap_eq_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    coordinateDecorationGap P hPrimitive hReduced u D =
      decorationGap P hPrimitive hReduced u D := by
  unfold coordinateDecorationGap decorationGap
  rw [
    sourceAffineFromCoordinates_eq_source,
    flatTopAffineFromCoordinates_eq_flatTop
  ]

/-- coordinate gap は decomposition-independent。 -/
theorem coordinateDecorationGap_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    coordinateDecorationGap P hPrimitive hReduced u D =
      coordinateDecorationGap P hPrimitive hReduced u E := by
  rw [
    coordinateDecorationGap_eq_decorationGap,
    coordinateDecorationGap_eq_decorationGap
  ]
  exact decorationGap_independent_of_decomposition
    P hPrimitive hReduced u D E

/-- three-layer decomposition を coordinate gap 版で再掲。 -/
theorem affineConst_eq_absoluteBase_add_boundaryGap_add_coordinateDecorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
      boundaryGap P hPrimitive hReduced u D +
      coordinateDecorationGap P hPrimitive hReduced u D := by
  rw [coordinateDecorationGap_eq_decorationGap]
  exact affineConst_eq_canonical_three_layer_decomposition
    P hPrimitive hReduced u D

/--
任意 top→bottom deletion trace を使った三層式でも、上段 residual は
coordinate gap として置き換えられる。
-/
theorem affineConst_eq_absoluteBase_add_traceCost_add_coordinateDecorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D)
      (retainNoBoundaries D) c) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
      c +
      coordinateDecorationGap P hPrimitive hReduced u D := by
  rw [coordinateDecorationGap_eq_decorationGap]
  exact affineConst_eq_absoluteBase_add_traceCost_add_decorationGap
    P hPrimitive hReduced u D T

/-! ## 7. fine arithmetic coordinates は Boolean coarsening 中に固定 -/

/--
一つの Boolean state に canonical flat geometry と actual source の fine arithmetic
coordinate vector を同時に載せる。

第二成分は pattern に依存しない。Boolean deletion は geometry だけを coarsen し、
actual fine arithmetic coordinates は固定したままにする。
-/
def arithmeticDecoratedBooleanState
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    FiberPoint P.oddCount P.twoDepth × List (ℕ × ℕ) :=
  (canonicalFlatPoint P hPrimitive hReduced u D R,
    arithmeticDecorationCoordinates D)

/-- Boolean pattern を変えても fine arithmetic coordinate vector は不変。 -/
theorem arithmeticCoordinates_fixed_across_boolean_states
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    (arithmeticDecoratedBooleanState
      P hPrimitive hReduced u D R).2 =
      (arithmeticDecoratedBooleanState
        P hPrimitive hReduced u D S).2 := by
  rfl

/--
## 主定理 2: decorated Boolean state は decomposition transport に対して canonical

対応する Boolean state の flat geometry も fine arithmetic coordinates も同時に一致する。
-/
theorem arithmeticDecoratedBooleanState_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    arithmeticDecoratedBooleanState
        P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R) =
      arithmeticDecoratedBooleanState
        P hPrimitive hReduced u D R := by
  apply Prod.ext
  · exact canonicalFlatPoint_transport
      P hPrimitive hReduced u D E R
  · exact
      (arithmeticDecorationCoordinates_independent_of_decomposition D E).symm

/-! ## 8. closure package -/

/--
Arithmetic Decoration Coordinates 層で閉じた事実を一つにまとめる。
-/
structure ArithmeticDecorationCoordinatesClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  lengths_exact :
    (arithmeticDecorationCoordinates D).map Prod.fst = D.lengths
  source_affine_exact :
    sourceAffineFromCoordinates u D = affineConst u.word
  flat_lengths_exact :
    (canonicalFlatTopCoordinates
      P hPrimitive hReduced u D).map Prod.fst = D.lengths
  flat_affine_exact :
    flatTopAffineFromCoordinates P hPrimitive hReduced u D =
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word
  coordinate_gap_exact :
    coordinateDecorationGap P hPrimitive hReduced u D =
      decorationGap P hPrimitive hReduced u D
  boolean_coordinates_fixed :
    ∀ R S : RetainedBoundaryPattern D,
      (arithmeticDecoratedBooleanState
        P hPrimitive hReduced u D R).2 =
        (arithmeticDecoratedBooleanState
          P hPrimitive hReduced u D S).2

/--
## Arithmetic Decoration Coordinates closure theorem

actual source の record decoration は canonical local translation coordinates を持ち、
その weighted reconstruction と canonical flat baseline の差は existing `decorationGap`
そのもの。Boolean coarsening はこの fine coordinate vector を変更しない。
-/
theorem arithmeticDecorationCoordinates_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ArithmeticDecorationCoordinatesClosed
      P hPrimitive hReduced u D := by
  refine {
    lengths_exact := arithmeticDecorationCoordinates_lengths D
    source_affine_exact := sourceAffineFromCoordinates_eq_source u D
    flat_lengths_exact := canonicalFlatTopCoordinates_lengths
      P hPrimitive hReduced u D
    flat_affine_exact := flatTopAffineFromCoordinates_eq_flatTop
      P hPrimitive hReduced u D
    coordinate_gap_exact := coordinateDecorationGap_eq_decorationGap
      P hPrimitive hReduced u D
    boolean_coordinates_fixed := ?_
  }
  intro R S
  exact arithmeticCoordinates_fixed_across_boolean_states
    P hPrimitive hReduced u D R S

end RecordFerrers
end Collatz2
