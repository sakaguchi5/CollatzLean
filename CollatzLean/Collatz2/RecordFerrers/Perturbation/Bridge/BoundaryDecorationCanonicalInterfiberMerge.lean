import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMerge

/-!
# Record–Ferrers Perturbation / Canonical Interfiber Merge

`BoundaryDecorationInterfiberMerge` では、`S.Le R` に対して P29 の actual coarsening
existence から target を `Classical.choose` で選ぶ transport を構成した。
これは到達可能性の存在を示すには十分だが、局所作用・合成則・diamond を map 自体から
読むには弱い。

本ファイルでは bundle の exact local-area product coordinates を使い、target coordinate を
直接再帰的に構成する choice-free canonical coarsening を導入する。

Bool flag の意味は length coarsening と完全に同じである。

* `true`  : current local-area factor をそのまま保存する。
* `false` : current factor と、tail を先に coarse 化して得た先頭 factor を吸収し、
            merged factor を flat local-area value `0` に置換する。

従って consecutive false flags は一つの大きな merged block を作り、その factor は flat になる。
この再帰は `coarsenByFlags` と型レベルで同期するため、任意 `S.Le R` について

  BoundaryDecorationFiber D R -> BoundaryDecorationFiber D S

を path や existential target selection を使わずに直接定義できる。

actual target は target fiber の exact equivalence の逆写像で realization する。
ここで非計算性が残るのは既存 local-area equivalence の witness 復号だけであり、
inter-fiber target 自体を existence theorem から任意選択しているわけではない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. local-area tuple の canonical coarse operation -/

namespace LocalAreaTuple

/-- positive length の canonical flat local-area spectrum point。 -/
def flatAreaValue
    (r : ℕ)
    (hr : 0 < r) : LocalAreaValue r :=
  (localFlatDecoration r hr).toAreaValue

@[simp] theorem flatAreaValue_val
    (r : ℕ)
    (hr : 0 < r) :
    (flatAreaValue r hr).1 = 0 := by
  change localDecorationArea (localFlatDecoration r hr).word = 0
  exact localDecorationArea_localFlatDecoration_eq_zero r hr

/--
先頭 length `r` を既に coarse 化された non-dependent tail の先頭へ吸収し、
吸収された新しい先頭 factor を flat にする。

`xs = []` も全関数化のため扱い、その場合は `[r]` の flat factorを返す。
通常の valid Bool coarsening の false branch では tail は nonempty である。
-/
def mergeHeadFlat
    (r : ℕ)
    (hr : 0 < r) :
    (xs : List ℕ) ->
      (∀ x ∈ xs, 0 < x) ->
      LocalAreaTuple xs ->
      LocalAreaTuple (mergeHeadLength r xs)
  | [], _hPos, .nil =>
      .cons (flatAreaValue r hr) .nil
  | x :: xs, hPos, .cons _a as =>
      .cons
        (flatAreaValue (r + x) (by
          have hx : 0 < x := hPos x (by simp)
          omega))
        as

/--
length coarsening と exact に同期する canonical local-area coarsening。

false branch では head decoration 情報を捨て、tail coarse result の先頭と merge して
新しい merged factor を flat area 0 に固定する。
-/
def canonicalCoarsen :
    (rs : List ℕ) ->
      (∀ r ∈ rs, 0 < r) ->
      (flags : List Bool) ->
      LocalAreaTuple rs ->
      LocalAreaTuple (coarsenByFlags rs flags)
  | [], _hPos, _flags, .nil =>
      .nil
  | [r], _hPos, _flags, .cons a .nil =>
      .cons a .nil
  | r :: s :: rest, hPos, [], A =>
      A
  | r :: s :: rest, hPos, true :: flags, .cons a (.cons b tail) =>
      let hTailPos : ∀ x ∈ (s :: rest), 0 < x := by
        intro x hx
        exact hPos x (by simp [hx])
      .cons a
        (canonicalCoarsen
          (s :: rest) hTailPos flags (.cons b tail))
  | r :: s :: rest, hPos, false :: flags, .cons _a (.cons b tail) =>
      let hr : 0 < r := hPos r (by simp)
      let hTailPos : ∀ x ∈ (s :: rest), 0 < x := by
        intro x hx
        exact hPos x (by simp [hx])
      let U := canonicalCoarsen
        (s :: rest) hTailPos flags (.cons b tail)
      let hOutPos :
          ∀ x ∈ coarsenByFlags (s :: rest) flags, 0 < x :=
        coarsenByFlags_all_pos flags hTailPos
      mergeHeadFlat r hr
        (coarsenByFlags (s :: rest) flags)
        hOutPos U

/-! ## 2. underlying area-vector evaluator -/

/-- merged group の先頭 value を flat 0 に置換する。 -/
def flattenHeadAreaValues : List ℕ -> List ℕ
  | [] => [0]
  | _ :: xs => 0 :: xs

/--
`canonicalCoarsen` の pure area-vector counterpart。
length list を忘れた後も同じ true/preserve, false/flatten-merge rule を保持する。
-/
def canonicalCoarsenValues : List ℕ -> List Bool -> List ℕ
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: rest, [] => a :: b :: rest
  | a :: b :: rest, true :: flags =>
      a :: canonicalCoarsenValues (b :: rest) flags
  | _a :: b :: rest, false :: flags =>
      flattenHeadAreaValues
        (canonicalCoarsenValues (b :: rest) flags)

@[simp] theorem flattenHeadAreaValues_idem
    (xs : List ℕ) :
    flattenHeadAreaValues (flattenHeadAreaValues xs) =
      flattenHeadAreaValues xs := by
  cases xs <;> rfl

/-- `mergeHeadFlat` は area vector の先頭を exact に 0 へ置換する。 -/
theorem mergeHeadFlat_values
    (r : ℕ)
    (hr : 0 < r)
    (xs : List ℕ)
    (hPos : ∀ x ∈ xs, 0 < x)
    (A : LocalAreaTuple xs) :
    (mergeHeadFlat r hr xs hPos A).values =
      flattenHeadAreaValues A.values := by
  cases xs with
  | nil =>
      cases A
      change
        (flatAreaValue r hr).1 :: [] = [0]
      rw [flatAreaValue_val]
  | cons x xs =>
      cases A with
      | cons a as =>
          change
            (flatAreaValue (r + x) _).1 :: as.values =
              0 :: as.values
          rw [flatAreaValue_val]

/--
先頭 boundary を保持する場合、
canonical coarsening の area vector は先頭 area をそのまま保持し、
tail の pure evaluator 一致をそのまま持ち上げる。
-/
private theorem canonicalCoarsen_values_true_step
    (r s : ℕ)
    (tail : List ℕ)
    (hPos : ∀ x ∈ r :: s :: tail, 0 < x)
    (more : List Bool)
    (a : LocalAreaValue r)
    (b : LocalAreaValue s)
    (bs : LocalAreaTuple tail)
    (hTailPos : ∀ x ∈ s :: tail, 0 < x)
    (hTail :
      (canonicalCoarsen
          (s :: tail) hTailPos more (.cons b bs)).values =
        canonicalCoarsenValues
          (b.1 :: bs.values) more) :
    (canonicalCoarsen
        (r :: s :: tail) hPos (true :: more)
        (.cons a (.cons b bs))).values =
      canonicalCoarsenValues
        (a.1 :: b.1 :: bs.values) (true :: more) := by
  change
    a.1 ::
        (canonicalCoarsen
          (s :: tail) hTailPos more (.cons b bs)).values =
      a.1 ::
        canonicalCoarsenValues
          (b.1 :: bs.values) more
  exact congrArg (List.cons a.1) hTail

/--
先頭 boundary を削除する場合、
tail を先に canonical coarsening した後、その先頭 factor を head と merge して
area 0 に平坦化する。

従って tuple 側の `mergeHeadFlat` は pure vector 側の
`flattenHeadAreaValues` と exact に対応する。
-/
private theorem canonicalCoarsen_values_false_step
    (r s : ℕ)
    (tail : List ℕ)
    (hPos : ∀ x ∈ r :: s :: tail, 0 < x)
    (more : List Bool)
    (a : LocalAreaValue r)
    (b : LocalAreaValue s)
    (bs : LocalAreaTuple tail)
    (hTailPos : ∀ x ∈ s :: tail, 0 < x)
    (hTail :
      (canonicalCoarsen
          (s :: tail) hTailPos more (.cons b bs)).values =
        canonicalCoarsenValues
          (b.1 :: bs.values) more) :
    (canonicalCoarsen
        (r :: s :: tail) hPos (false :: more)
        (.cons a (.cons b bs))).values =
      canonicalCoarsenValues
        (a.1 :: b.1 :: bs.values) (false :: more) := by
  let hr : 0 < r :=
    hPos r (by simp)
  let hOutPos :
      ∀ x ∈ coarsenByFlags (s :: tail) more, 0 < x :=
    coarsenByFlags_all_pos more hTailPos
  change
    (mergeHeadFlat
        r hr
        (coarsenByFlags (s :: tail) more)
        hOutPos
        (canonicalCoarsen
          (s :: tail) hTailPos more (.cons b bs))).values =
      flattenHeadAreaValues
        (canonicalCoarsenValues
          (b.1 :: bs.values) more)
  rw [mergeHeadFlat_values]
  rw [hTail]

/--
canonical tuple coarsening の underlying area vector は、
length index を忘れて area vector だけに作用させた
`canonicalCoarsenValues` と exact に一致する。

`true` branch では先頭 area を保存し、
`false` branch では tail を先に粗視化した後、
merged group の先頭 area を 0 に平坦化する。
-/
theorem canonicalCoarsen_values
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r)
    (flags : List Bool)
    (A : LocalAreaTuple rs) :
    (canonicalCoarsen rs hPos flags A).values =
      canonicalCoarsenValues A.values flags := by
  induction rs generalizing flags  with
  | nil =>
      cases A
      simp only [
        canonicalCoarsen,
        canonicalCoarsenValues,
        values_nil
      ]
      rfl
  | cons r rest ih =>
      cases rest with
      | nil =>
          cases A with
          | cons a as =>
              cases as
              simp only [
                canonicalCoarsen,
                canonicalCoarsenValues,
                values_cons,
                values_nil
              ]
              rfl
      | cons s tail =>
          cases A with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases flags with
                  | nil =>
                      rfl
                  | cons keep more =>
                      have hTailPos :
                          ∀ x ∈ s :: tail, 0 < x := by
                        intro x hx
                        exact hPos x (by simp [hx])
                      have hTail :
                          (canonicalCoarsen
                              (s :: tail)
                              hTailPos
                              more
                              (.cons b bs)).values =
                            canonicalCoarsenValues
                              (b.1 :: bs.values)
                              more := by
                        exact
                          ih hTailPos more (.cons b bs)
                      cases keep with
                      | true =>
                          exact
                            canonicalCoarsen_values_true_step
                              r s tail
                              hPos more
                              a b bs
                              hTailPos hTail
                      | false =>
                          exact
                            canonicalCoarsen_values_false_step
                              r s tail
                              hPos more
                              a b bs
                              hTailPos hTail

/-- LocalAreaTuple は underlying area vector から lossless に復元できる。 -/
theorem eq_of_values_eq
    {rs : List ℕ}
    {A B : LocalAreaTuple rs}
    (h : A.values = B.values) :
    A = B := by
  induction A with
  | nil =>
      cases B
      rfl
  | @cons r rs a as ih =>
      cases B with
      | cons b bs =>
          simp only [values_cons, List.cons.injEq] at h
          have hab : a = b := Subtype.ext h.1
          subst b
          have hTail : as = bs := ih h.2
          subst bs
          rfl

end LocalAreaTuple

/-! ## 3. Boolean base 上の canonical inter-fiber coarsening -/

/--
`S.Le R` に対する canonical abstract fiber map。

current base `R` の coarse skeleton 上で relative boundary flags を一度だけ読み、
`LocalAreaTuple.canonicalCoarsen` により target coarse skeleton へ移す。
最後に relative coarsening composition が与える index equality に沿って cast する。

この写像は `RecordDecomposition D` と Boolean boundary order だけから定まり、
`ContractingExponentPair`、primitive / reduced 仮定、actual source point には依存しない。
-/
def boundaryDecorationCanonicalInterfiberCoarsening
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    BoundaryDecorationFiber D R →
      BoundaryDecorationFiber D S :=
  fun A =>
    LocalAreaTuple.cast
      (relativeBoundaryFlags_spec D hSR).2
      (LocalAreaTuple.canonicalCoarsen
        (coarsenedLengthsFor D R)
        (coarsenedLengthsFor_pos D R)
        (relativeBoundaryFlags R S)
        A)

/--
retained boundary 一個を削除する canonical abstract inter-fiber merge。

`eraseRetainedBoundary R b ≤ R` に対する
`boundaryDecorationCanonicalInterfiberCoarsening` の one-boundary specialization。
この写像も Boolean boundary data と `D` の coarse skeleton のみに依存する。
-/
def boundaryDecorationCanonicalInterfiberMerge
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D) :
    BoundaryDecorationFiber D R →
      BoundaryDecorationFiber D (eraseRetainedBoundary R b) :=
  boundaryDecorationCanonicalInterfiberCoarsening
    D (eraseRetainedBoundary_le R b)

/--
canonical abstract target を target actual fiber equivalence の逆写像で realization する。

abstract inter-fiber coarsening 自体は `D` と Boolean boundary data のみに依存し、
ここで初めて primitive / reduced data により与えられる
`boundaryDecorationFiberEquiv` を使って actual point へ transport する。

existence theorem から inter-fiber target point を choose しない。
-/
noncomputable def boundaryDecorationActualCanonicalInterfiberCoarsening
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D S :=
  (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D S).symm
    (boundaryDecorationCanonicalInterfiberCoarsening
      D hSR
      (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R X))

/--
one-boundary canonical actual merge。

abstract one-boundary coarseningを
source / target actual fiber equivalence を通して realization したもの。
-/
noncomputable def boundaryDecorationActualCanonicalInterfiberMerge
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D
      (eraseRetainedBoundary R b) :=
  boundaryDecorationActualCanonicalInterfiberCoarsening
    P hPrimitive hReduced u D
    (eraseRetainedBoundary_le R b) X

/--
canonical actual inter-fiber target を abstract coordinate に戻すと、
定義した canonical abstract target と exact に一致する。

したがって actual realization は abstract coarsening の coordinate を
一切変更しない exact transport である。
-/
theorem boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D S
        (boundaryDecorationActualCanonicalInterfiberCoarsening
          P hPrimitive hReduced u D hSR X) =
      boundaryDecorationCanonicalInterfiberCoarsening
        D hSR
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X) := by
  unfold boundaryDecorationActualCanonicalInterfiberCoarsening
  exact (boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D S).apply_symm_apply _

/--
one-boundary canonical abstract merge を base と fiber coordinate の組として束ね、
`BoundaryDecorationBundle D` の point を作る。
-/
def boundaryDecorationBundleCanonicalInterfiberMerge
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (A : BoundaryDecorationFiber D R) :
    BoundaryDecorationBundle D :=
  ⟨eraseRetainedBoundary R b,
    boundaryDecorationCanonicalInterfiberMerge
      D R b A⟩

@[simp] theorem boundaryDecorationBundleCanonicalInterfiberMerge_base
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (A : BoundaryDecorationFiber D R) :
    (boundaryDecorationBundleCanonicalInterfiberMerge
      D R b A).1 =
      eraseRetainedBoundary R b := rfl

/-! ## 4. closure -/

/--
canonical inter-fiber coarsening 層の closure package。

`downward_map` と `one_boundary_map` は
`RecordDecomposition D` と Boolean boundary order のみから定まる abstract maps を保持する。

`actual_coordinate_exact` では、それらの pure abstract maps を
primitive / reduced data により与えられる actual fiber equivalence で realization しても、
abstract coordinate が exact に保存されることを保持する。
-/
structure BoundaryDecorationCanonicalInterfiberMergeClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where

  downward_map :
    ∀ {R S : RetainedBoundaryPattern D},
      S.Le R →
      Nonempty
        (BoundaryDecorationFiber D R →
          BoundaryDecorationFiber D S)

  one_boundary_map :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D),
      Nonempty
        (BoundaryDecorationFiber D R →
          BoundaryDecorationFiber D
            (eraseRetainedBoundary R b))

  actual_coordinate_exact :
    ∀ {R S : RetainedBoundaryPattern D}
      (hSR : S.Le R)
      (X : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D S
          (boundaryDecorationActualCanonicalInterfiberCoarsening
            P hPrimitive hReduced u D hSR X) =
        boundaryDecorationCanonicalInterfiberCoarsening
          D hSR
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X)

/--
canonical inter-fiber layer closure theorem。

Boolean boundary order が与える pure abstract downward coarsening と
one-boundary merge の存在、およびそれを actual fibers へ transport したときの
coordinate exactness を同時に束ねる。
-/
theorem boundaryDecorationCanonicalInterfiberMerge_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationCanonicalInterfiberMergeClosed
      P hPrimitive hReduced u D := by
  refine {
    downward_map := ?_
    one_boundary_map := ?_
    actual_coordinate_exact := ?_
  }
  · intro R S hSR
    exact ⟨boundaryDecorationCanonicalInterfiberCoarsening
      D hSR⟩
  · intro R b
    exact ⟨boundaryDecorationCanonicalInterfiberMerge
      D R b⟩
  · intro R S hSR X
    exact boundaryDecorationActualCanonicalInterfiberCoarsening_coordinate
      P hPrimitive hReduced u D hSR X

end RecordFerrers
end Collatz2
