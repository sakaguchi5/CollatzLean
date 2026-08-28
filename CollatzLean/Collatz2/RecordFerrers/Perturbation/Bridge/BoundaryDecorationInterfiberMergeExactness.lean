import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalInterfiberMerge

/-!
# Record–Ferrers Perturbation / Interfiber Merge Exactness

`BoundaryDecorationCanonicalInterfiberMerge` で、Bool coarse rule と同期する
choice-free canonical local-area transport を構成した。

本ファイルではその作用を lossless area vector と genuine fixed-fiber arithmetic へ読み戻す。

主な内容は次の通り。

* index cast は area vector を変えない。
* canonical `R -> S` transport の target area vector は
  `canonicalCoarsenValues source.values (relativeBoundaryFlags R S)` と exact に一致する。
* false branch は merged group の先頭 local-area coordinate を exact に `0` へ置換する。
* actual canonical target を area-product coordinate に戻すと上の abstract targetそのものになる。
* bundle realization 上の affine loss は bundle total excess の差と exact に一致する。
* genuine one-boundary deletion では base boundary count が exact に一つ減る。

従って canonical inter-fiber merge は、単なる target-skeleton existence ではなく、
local-area coordinates と genuine arithmetic の双方で作用が完全に追跡できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. area-vector exactness -/

namespace LocalAreaTuple

/-- dependent index cast は underlying area vector を変えない。 -/
theorem cast_values
    {rs ss : List ℕ}
    (h : rs = ss)
    (A : LocalAreaTuple rs) :
    (cast h A).values = A.values := by
  subst ss
  rfl

/-- false branch は merged head area を exact に 0 にする。 -/
@[simp] theorem canonicalCoarsenValues_false
    (a b : ℕ)
    (rest : List ℕ)
    (flags : List Bool) :
    canonicalCoarsenValues
        (a :: b :: rest) (false :: flags) =
      flattenHeadAreaValues
        (canonicalCoarsenValues (b :: rest) flags) := rfl

/-- true branch は head area を exact に保存する。 -/
@[simp] theorem canonicalCoarsenValues_true
    (a b : ℕ)
    (rest : List ℕ)
    (flags : List Bool) :
    canonicalCoarsenValues
        (a :: b :: rest) (true :: flags) =
      a :: canonicalCoarsenValues (b :: rest) flags := rfl

/-- flatten された nonempty vector の先頭は 0。 -/
@[simp] theorem flattenHeadAreaValues_head
    {a : ℕ}
    {rest : List ℕ} :
    (flattenHeadAreaValues (a :: rest)).head? = some 0 := rfl

end LocalAreaTuple

/--
## Canonical Fiber Coordinate Exactness

canonical `R → S` abstract transport の area vector は、
relative boundary flags に対する pure recursive evaluator
`LocalAreaTuple.canonicalCoarsenValues` と exact に一致する。

この formula は `D` と Boolean boundary data のみから定まり、
`ContractingExponentPair` や primitive / reduced data、
actual source point には依存しない。
-/
theorem boundaryDecorationCanonicalInterfiberCoarsening_values
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (A : BoundaryDecorationFiber D R) :
    (boundaryDecorationCanonicalInterfiberCoarsening
        D hSR A).values =
      LocalAreaTuple.canonicalCoarsenValues
        A.values (relativeBoundaryFlags R S) := by
  unfold boundaryDecorationCanonicalInterfiberCoarsening
  rw [LocalAreaTuple.cast_values]
  exact LocalAreaTuple.canonicalCoarsen_values
    (coarsenedLengthsFor D R)
    (coarsenedLengthsFor_pos D R)
    (relativeBoundaryFlags R S)
    A

/--
one-boundary canonical abstract merge の area-vector formula。

一個の retained boundary を削除する merge は、
対応する relative boundary flags に対する
`canonicalCoarsenValues` そのものとして計算される。
-/
theorem boundaryDecorationCanonicalInterfiberMerge_values
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (A : BoundaryDecorationFiber D R) :
    (boundaryDecorationCanonicalInterfiberMerge
        D R b A).values =
      LocalAreaTuple.canonicalCoarsenValues
        A.values
        (relativeBoundaryFlags R (eraseRetainedBoundary R b)) := by
  exact boundaryDecorationCanonicalInterfiberCoarsening_values
    D (eraseRetainedBoundary_le R b) A

/-! ## 2. actual realization exactness -/

/--
one-boundary canonical actual target を abstract fiber coordinate に戻すと、
pure canonical abstract merge そのものに exact に一致する。

すなわち actual realization は abstract merge の coordinate を変更しない。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_coordinate
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X) =
      boundaryDecorationCanonicalInterfiberMerge
        D R b
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X) := by
  exact boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b) X

/--
one-boundary canonical actual merge target の area vector も、
source actual point を abstract coordinate に移した後の
pure recursive evaluator と exact に一致する。

したがって actual realization を経由しても
canonical coarsening の area-vector formula は完全に保存される。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_values
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X)).values =
      LocalAreaTuple.canonicalCoarsenValues
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X).values
        (relativeBoundaryFlags R (eraseRetainedBoundary R b)) := by
  rw [boundaryDecorationActualCanonicalInterfiberMerge_coordinate]
  exact boundaryDecorationCanonicalInterfiberMerge_values
    D R b
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R X)

/-! ## 3. bundle realization と arithmetic loss -/

/--
arbitrary downward canonical abstract target を
base pattern と fiber coordinate の組として `BoundaryDecorationBundle` に package する。

この construction 自体は Boolean base と abstract fiber のみに依存し、
actual realization や primitive / reduced data は用いない。
-/
def boundaryDecorationBundleCanonicalInterfiberCoarsening
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (A : BoundaryDecorationFiber D R) :
    BoundaryDecorationBundle D :=
  ⟨S,
    boundaryDecorationCanonicalInterfiberCoarsening
      D hSR A⟩

@[simp] theorem boundaryDecorationBundleCanonicalInterfiberCoarsening_base
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (A : BoundaryDecorationFiber D R) :
    (boundaryDecorationBundleCanonicalInterfiberCoarsening
      D hSR A).1 = S := rfl

/--
canonical downward move に伴う arithmetic loss。

source bundle と canonical abstract target bundle の
`boundaryDecorationBundleTotalExcess` の自然数差として定義する。

canonical inter-fiber map 自体は pure abstract だが、
ここでは bundle total excess を評価するため
`P` と primitive / reduced data が初めて必要になる。
-/
def boundaryDecorationCanonicalInterfiberLoss
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (A : BoundaryDecorationFiber D R) : ℕ :=
  boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D ⟨R, A⟩ -
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D
      (boundaryDecorationBundleCanonicalInterfiberCoarsening
        D hSR A)

/--
## Arithmetic Loss Exactness

canonical `R → S` move の source / target canonical realizationsの
genuine affine difference は、
bundle total-excess difference と exact に一致する。

inter-fiber target 自体は pure abstract coarsening で構成され、
その source / target bundle を actual arithmetic realization へ移したときの差を
`boundaryDecorationCanonicalInterfiberLoss` が exact に測る。

ここでは strict descent を仮定しない。
Nat subtraction の equality として既存 bundle arithmetic exactness から得る。
-/
theorem boundaryDecorationCanonicalInterfiber_affineLoss_exact
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (A : BoundaryDecorationFiber D R) :
    affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D ⟨R, A⟩).word -
      affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D
          (boundaryDecorationBundleCanonicalInterfiberCoarsening
            D hSR A)).word =
      boundaryDecorationCanonicalInterfiberLoss
        P hPrimitive hReduced u D hSR A := by
  rw [
    boundaryDecorationBundleRealization_affineConst
      P hPrimitive hReduced u D ⟨R, A⟩,
    boundaryDecorationBundleRealization_affineConst
      P hPrimitive hReduced u D
      (boundaryDecorationBundleCanonicalInterfiberCoarsening
        D hSR A)
  ]
  unfold boundaryDecorationCanonicalInterfiberLoss
  omega

/--
one-boundary canonical merge は retained boundary count を exact に一つ減らす。
この事実は fiber coordinate や actual arithmetic realization に依存しない
pure Boolean-base の count identity。
-/
theorem boundaryDecorationCanonicalInterfiberMerge_boundaryCount
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    retainedBoundaryCount D (eraseRetainedBoundary R b) + 1 =
      retainedBoundaryCount D R :=
  retainedBoundaryCount_erase_add_one R b hb

/-! ## 4. closure -/

/--
inter-fiber merge exactness 層の closure package。

`coordinate_formula` は Boolean base 上の pure abstract coarsening formula、
`actual_coordinate_formula` はその actual realization における coordinate exactness、
`affine_loss_exact` はさらに arithmetic realization まで加えた loss exactness を保持する。

したがって

pure abstract coarsening
→ actual realization
→ arithmetic realization

という三層の exactness を一つに束ねる。
-/
structure BoundaryDecorationInterfiberMergeExactnessClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where

  coordinate_formula :
    ∀ {R S : RetainedBoundaryPattern D}
      (hSR : S.Le R)
      (A : BoundaryDecorationFiber D R),
      (boundaryDecorationCanonicalInterfiberCoarsening
          D hSR A).values =
        LocalAreaTuple.canonicalCoarsenValues
          A.values (relativeBoundaryFlags R S)

  actual_coordinate_formula :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D)
      (X : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b)
          (boundaryDecorationActualCanonicalInterfiberMerge
            P hPrimitive hReduced u D R b X)).values =
        LocalAreaTuple.canonicalCoarsenValues
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).values
          (relativeBoundaryFlags R (eraseRetainedBoundary R b))

  affine_loss_exact :
    ∀ {R S : RetainedBoundaryPattern D}
      (hSR : S.Le R)
      (A : BoundaryDecorationFiber D R),
      affineConst
          (boundaryDecorationBundleRealization
            P hPrimitive hReduced u D ⟨R, A⟩).word -
        affineConst
          (boundaryDecorationBundleRealization
            P hPrimitive hReduced u D
            (boundaryDecorationBundleCanonicalInterfiberCoarsening
              D hSR A)).word =
        boundaryDecorationCanonicalInterfiberLoss
          P hPrimitive hReduced u D hSR A

/--
Interfiber merge exactness closure theorem。

pure abstract canonical coarsening の coordinate formula、
その actual realization の coordinate exactness、
さらに canonical source / target realizations 間の arithmetic loss exactness を
一つの closure package として確立する。
-/
theorem boundaryDecorationInterfiberMergeExactness_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationInterfiberMergeExactnessClosed
      P hPrimitive hReduced u D := by
  refine {
    coordinate_formula := ?_
    actual_coordinate_formula := ?_
    affine_loss_exact := ?_
  }
  · intro R S hSR A
    exact boundaryDecorationCanonicalInterfiberCoarsening_values
      D hSR A
  · intro R b X
    exact boundaryDecorationActualCanonicalInterfiberMerge_values
      P hPrimitive hReduced u D R b X
  · intro R S hSR A
    exact boundaryDecorationCanonicalInterfiber_affineLoss_exact
      P hPrimitive hReduced u D hSR A

end RecordFerrers
end Collatz2
