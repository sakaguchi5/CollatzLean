import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DeletionPotentialCocycle

/-!
# Record–Ferrers Perturbation / Boolean Family Canonicity

`ArithmeticDecorationCanonicity` では、同じ actual source に対する
`canonicalFlatTop` / `boundaryGap` / `decorationGap` が
`RecordDecomposition` の選択に依存しないことを示した。

`DeletionPotentialCocycle` では、選んだ decomposition `D` の上で
Boolean deletion family に genuine `affineConst` の path-independent cocycle を載せた。

まだ残っていたのは、Boolean family 自体の型が

  RetainedBoundaryPattern D

のように decomposition `D` に依存していたことである。

本ファイルでは、既存の

  RecordDecomposition.lengths_unique D E : D.lengths = E.lengths

を使って、同じ actual source の任意の二 decomposition `D,E` の間に
canonical transport を作る。そして transport が

* 全保持 / 全消去
* meet / join / complement
* Boolean 順序
* coarse length skeleton
* canonical flat FiberPoint
* flat affine potential
* deletion cost / boundary potential
* actual deletion reachability
* cost 付き deletion trace

をすべて exact に保存することを示す。

従って `D` は Boolean family を記述するための witness にすぎず、
その Boolean / Ferrers / arithmetic deletion system 全体は actual source に内在する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. length skeleton equality に沿う pattern transport -/

/--
decomposition の length equality は、
内部境界を添字づける `Fin` の大きさの equality を与える。
-/
theorem internalRecordBoundarySize_eq_of_lengths_eq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths) :
    E.lengths.length - 1 = D.lengths.length - 1 := by
  exact congrArg
    (fun xs : List ℕ => xs.length - 1)
    hLengths.symm

/--
length equality に沿って、`E` の内部境界を
対応する `D` の内部境界へ戻す。
-/
def castInternalRecordBoundaryOfLengthsEq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (i : InternalRecordBoundary E) :
    InternalRecordBoundary D := by
  unfold InternalRecordBoundary at i ⊢
  exact Fin.cast
    (internalRecordBoundarySize_eq_of_lengths_eq D E hLengths)
    i

/--
二つの decomposition の length skeleton が等しいとき、
その内部境界 Boolean pattern を同じ位置の pattern として運ぶ。

`RetainedBoundaryPattern D` は定義上
`Fin (D.lengths.length - 1) → Bool` なので、length list equality だけで十分。
-/
def transportRetainedBoundaryPatternOfLengthsEq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D) :
    RetainedBoundaryPattern E := by
  intro i
  exact R
    (castInternalRecordBoundaryOfLengthsEq D E hLengths i)

@[simp] theorem transportRetainedBoundaryPatternOfLengthsEq_apply
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D)
    (i : InternalRecordBoundary E) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths R i =
      R (castInternalRecordBoundaryOfLengthsEq D E hLengths i) := by
  rfl

@[simp] theorem transportRetainedBoundaryPatternOfLengthsEq_refl
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPatternOfLengthsEq D D rfl R = R := by
  rfl

/-- length equality transport は全保持 pattern を全保持 pattern へ送る。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_all
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths (retainAllBoundaries D) =
      retainAllBoundaries E := by
  funext i
  rfl

/-- length equality transport は全消去 pattern を全消去 pattern へ送る。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_none
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths (retainNoBoundaries D) =
      retainNoBoundaries E := by
  funext i
  rfl

/-- meet は length equality transport と可換。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_meet
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R S : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths (retainedMeet R S) =
      retainedMeet
        (transportRetainedBoundaryPatternOfLengthsEq D E hLengths R)
        (transportRetainedBoundaryPatternOfLengthsEq D E hLengths S) := by
  funext i
  rfl

/-- join は length equality transport と可換。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_join
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R S : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths (retainedJoin R S) =
      retainedJoin
        (transportRetainedBoundaryPatternOfLengthsEq D E hLengths R)
        (transportRetainedBoundaryPatternOfLengthsEq D E hLengths S) := by
  funext i
  rfl

/-- complement は length equality transport と可換。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_complement
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths (retainedComplement R) =
      retainedComplement
        (transportRetainedBoundaryPatternOfLengthsEq D E hLengths R) := by
  funext i
  rfl

/--
length equality に沿って境界を往復 transport すると元に戻る。
-/
@[simp] theorem castInternalRecordBoundaryOfLengthsEq_roundtrip
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (i : InternalRecordBoundary D) :
    castInternalRecordBoundaryOfLengthsEq D E hLengths
        (castInternalRecordBoundaryOfLengthsEq
          E D hLengths.symm i) =
      i := by
  apply Fin.ext
  rfl

/-- Boolean inclusion order は length equality transport で exact に保存される。 -/
theorem transportRetainedBoundaryPatternOfLengthsEq_le_iff
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R S : RetainedBoundaryPattern D) :
    (transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths R).Le
      (transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths S) ↔
      R.Le S := by
  constructor
  · intro hTrans i hi
    let j : InternalRecordBoundary E :=
      castInternalRecordBoundaryOfLengthsEq
        E D hLengths.symm i
    have hjR :
        transportRetainedBoundaryPatternOfLengthsEq
            D E hLengths R j = true := by
      rw [transportRetainedBoundaryPatternOfLengthsEq_apply]
      simp [j]
      omega
    have hjS := hTrans j hjR
    rw [transportRetainedBoundaryPatternOfLengthsEq_apply] at hjS
    simpa [j] using hjS
  · intro hRS i hi
    rw [transportRetainedBoundaryPatternOfLengthsEq_apply] at hi ⊢
    exact hRS
      (castInternalRecordBoundaryOfLengthsEq
        D E hLengths i)
      hi

/--
decomposition の length equality は、
内部境界 index のサイズ equality を与える。
-/
theorem internalRecordBoundarySize_eq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths) :
    D.lengths.length - 1 =
      E.lengths.length - 1 := by
  exact congrArg
    (fun xs : List ℕ => xs.length - 1)
    hLengths

/--
length equality から作った境界 cast は、
標準の size equality による `Fin.cast` と一致する。

等式証明そのものの proof term には依存しない。
-/
theorem castInternalRecordBoundaryOfLengthsEq_eq_cast
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (i : InternalRecordBoundary E) :
    castInternalRecordBoundaryOfLengthsEq
        D E hLengths i =
      Fin.cast
        (internalRecordBoundarySize_eq D E hLengths).symm
        i := by
  apply Fin.ext
  rfl

/--
pattern transport は、対応する内部境界へ `Fin.cast` して
元 pattern を評価するだけ。
-/
theorem transportRetainedBoundaryPatternOfLengthsEq_apply_cast
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D)
    (i : InternalRecordBoundary E) :
    transportRetainedBoundaryPatternOfLengthsEq
        D E hLengths R i =
      R
        (Fin.cast
          (internalRecordBoundarySize_eq D E hLengths).symm
          i) := by
  rw [transportRetainedBoundaryPatternOfLengthsEq_apply]
  rw [castInternalRecordBoundaryOfLengthsEq_eq_cast
    D E hLengths i]

/--
length equality transport は retained Bool 列を変えない。
-/
theorem retainedFlags_transport_of_lengths_eq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D) :
    retainedFlags
        (transportRetainedBoundaryPatternOfLengthsEq
          D E hLengths R) =
      retainedFlags R := by
  unfold retainedFlags
  let hSize :
      D.lengths.length - 1 =
        E.lengths.length - 1 :=
    internalRecordBoundarySize_eq D E hLengths
  have hTransport :
      transportRetainedBoundaryPatternOfLengthsEq
          D E hLengths R =
        fun i =>
          R (Fin.cast hSize.symm i) := by
    funext i
    exact
      transportRetainedBoundaryPatternOfLengthsEq_apply_cast
        D E hLengths R i
  rw [hTransport]
  exact (List.ofFn_congr hSize R).symm

/-- coarse length skeleton そのものも transport で不変。 -/
theorem coarsenedLengthsFor_transport_of_lengths_eq
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (hLengths : D.lengths = E.lengths)
    (R : RetainedBoundaryPattern D) :
    coarsenedLengthsFor E
        (transportRetainedBoundaryPatternOfLengthsEq
          D E hLengths R) =
      coarsenedLengthsFor D R := by
  unfold coarsenedLengthsFor
  rw [retainedFlags_transport_of_lengths_eq
    D E hLengths R]
  exact congrArg
    (fun xs : List ℕ =>
      coarsenByFlags xs (retainedFlags R))
    hLengths.symm

/-! ## 2. genuine RecordDecomposition uniqueness による canonical transport -/

/--
同じ actual source の二 decomposition 間の canonical Boolean transport。
唯一性定理 `RecordDecomposition.lengths_unique` を内部で使う。
-/
def transportRetainedBoundaryPattern
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    RetainedBoundaryPattern E :=
  transportRetainedBoundaryPatternOfLengthsEq
    D E (RecordDecomposition.lengths_unique D E) R

/-- canonical transport は全保持を保つ。 -/
theorem transportRetainedBoundaryPattern_all
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1) :
    transportRetainedBoundaryPattern D E (retainAllBoundaries D) =
      retainAllBoundaries E := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_all
    D E (RecordDecomposition.lengths_unique D E)

/-- canonical transport は全消去を保つ。 -/
theorem transportRetainedBoundaryPattern_none
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1) :
    transportRetainedBoundaryPattern D E (retainNoBoundaries D) =
      retainNoBoundaries E := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_none
    D E (RecordDecomposition.lengths_unique D E)

/-- canonical transport は meet を保つ。 -/
theorem transportRetainedBoundaryPattern_meet
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPattern D E (retainedMeet R S) =
      retainedMeet
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_meet
    D E (RecordDecomposition.lengths_unique D E) R S

/-- canonical transport は join を保つ。 -/
theorem transportRetainedBoundaryPattern_join
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPattern D E (retainedJoin R S) =
      retainedJoin
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_join
    D E (RecordDecomposition.lengths_unique D E) R S

/-- canonical transport は complement を保つ。 -/
theorem transportRetainedBoundaryPattern_complement
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPattern D E (retainedComplement R) =
      retainedComplement (transportRetainedBoundaryPattern D E R) := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_complement
    D E (RecordDecomposition.lengths_unique D E) R

/-- canonical transport は Boolean order を exact に保存する。 -/
theorem transportRetainedBoundaryPattern_le_iff
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    (transportRetainedBoundaryPattern D E R).Le
        (transportRetainedBoundaryPattern D E S) ↔
      R.Le S := by
  unfold transportRetainedBoundaryPattern
  exact transportRetainedBoundaryPatternOfLengthsEq_le_iff
    D E (RecordDecomposition.lengths_unique D E) R S

/-- canonical transport 後も coarse length skeleton は exact に同じ。 -/
theorem coarsenedLengthsFor_transport
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    coarsenedLengthsFor E (transportRetainedBoundaryPattern D E R) =
      coarsenedLengthsFor D R := by
  unfold transportRetainedBoundaryPattern
  exact coarsenedLengthsFor_transport_of_lengths_eq
    D E (RecordDecomposition.lengths_unique D E) R

/-- D→E→D と往復すると元の pattern に exact に戻る。 -/
theorem transportRetainedBoundaryPattern_roundtrip
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    transportRetainedBoundaryPattern E D
        (transportRetainedBoundaryPattern D E R) = R := by
  apply coarsenedLengthsFor_injective D
  rw [
    coarsenedLengthsFor_transport E D
      (transportRetainedBoundaryPattern D E R),
    coarsenedLengthsFor_transport D E R
  ]

/--
同じ actual source の二 decomposition が与える Boolean cube の canonical equivalence。
-/
def retainedBoundaryPatternEquiv
    {p H : ℕ}
    {u : FiberPoint p H}
    (D E : RecordDecomposition u 1) :
    RetainedBoundaryPattern D ≃ RetainedBoundaryPattern E where
  toFun := transportRetainedBoundaryPattern D E
  invFun := transportRetainedBoundaryPattern E D
  left_inv := transportRetainedBoundaryPattern_roundtrip D E
  right_inv := transportRetainedBoundaryPattern_roundtrip E D

/-! ## 3. canonical flat geometry の decomposition-independence -/

/--
対応する Boolean pattern は同じ coarse skeleton を持つので、
P30 の canonical flat FiberPoint 自体が exact に一致する。
-/
theorem canonicalFlatPoint_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    canonicalFlatPoint P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R) =
      canonicalFlatPoint P hPrimitive hReduced u D R := by
  apply FiberPoint.toFerrersShape_injective
  apply FerrersShape.ext
  intro i
  change
    (canonicalFlatPoint P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)).excessAt i.1 =
      (canonicalFlatPoint P hPrimitive hReduced u D R).excessAt i.1
  simp only [canonicalFlatPoint]
  rw [
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u E
      (transportRetainedBoundaryPattern D E R) i.isLt,
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u D R i.isLt,
    coarsenedLengthsFor_transport D E R
  ]

/-- 全保持 top は family transport の特殊例として exact に一致する。 -/
theorem canonicalFlatTop_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    canonicalFlatTop P hPrimitive hReduced u E =
      canonicalFlatTop P hPrimitive hReduced u D := by
  unfold canonicalFlatTop
  rw [← transportRetainedBoundaryPattern_all D E]
  exact canonicalFlatPoint_transport
    P hPrimitive hReduced u D E (retainAllBoundaries D)

/-- 全消去 bottom も family transport の特殊例として exact に一致する。 -/
theorem canonicalFlatBottom_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    canonicalFlatBottom P hPrimitive hReduced u E =
      canonicalFlatBottom P hPrimitive hReduced u D := by
  unfold canonicalFlatBottom canonicalNoBoundaryPoint
  rw [← transportRetainedBoundaryPattern_none D E]
  exact canonicalFlatPoint_transport
    P hPrimitive hReduced u D E (retainNoBoundaries D)

/-! ## 4. affine potential / cocycle の decomposition-independence -/

/-- corresponding flat point の genuine affine potential は exact に同じ。 -/
theorem flatAffine_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    flatAffine P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R) =
      flatAffine P hPrimitive hReduced u D R := by
  unfold flatAffine
  rw [canonicalFlatPoint_transport P hPrimitive hReduced u D E R]

/-- deletion cost は decomposition の選択に依存しない。 -/
theorem deletionCost_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    deletionCost P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) =
      deletionCost P hPrimitive hReduced u D R S := by
  unfold deletionCost
  rw [
    flatAffine_transport P hPrimitive hReduced u D E R,
    flatAffine_transport P hPrimitive hReduced u D E S
  ]

/-- top-relative boundary potential も corresponding pattern では exact に同じ。 -/
theorem boundaryPotential_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    boundaryPotential P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R) =
      boundaryPotential P hPrimitive hReduced u D R := by
  unfold boundaryPotential
  rw [← transportRetainedBoundaryPattern_all D E]
  exact deletionCost_transport
    P hPrimitive hReduced u D E (retainAllBoundaries D) R

/-! ## 5. actual reachability も canonical Boolean transport で不変 -/

/--
P35 の actual deletion reachability は Boolean order と exact に同値なので、
family transport によって reachability 自体も exact に保存される。
-/
theorem actualCanonicalDeletionReachable_transport_iff
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    ActualCanonicalDeletionReachable
        P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) ↔
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D R S := by
  rw [
    actualReachable_iff_retainedLe
      P hPrimitive hReduced u E
      (transportRetainedBoundaryPattern D E R)
      (transportRetainedBoundaryPattern D E S),
    actualReachable_iff_retainedLe
      P hPrimitive hReduced u D R S
  ]
  exact transportRetainedBoundaryPattern_le_iff D E S R

/-! ## 6. cost 付き trace も同じ total cost のまま transport できる -/

/--
D 上の cost 付き actual deletion trace を E 上へ運ぶ。

edge proof object を直接 transport せず、

1. trace から P35 reachability を忘却
2. reachability の decomposition-independence で E へ移送
3. E 上の cost trace の存在を取得
4. 両 trace の endpoint exactness と `deletionCost_transport` で total cost を同定

という経路を使う。
-/
theorem actualDeletionTraceCost_transport
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D R S c) :
    ActualDeletionTraceCost
      P hPrimitive hReduced u E
      (transportRetainedBoundaryPattern D E R)
      (transportRetainedBoundaryPattern D E S) c := by
  have hReachD :
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D R S :=
    ActualDeletionTraceCost.reachable
      P hPrimitive hReduced u D T
  have hReachE :
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) :=
    (actualCanonicalDeletionReachable_transport_iff
      P hPrimitive hReduced u D E R S).2 hReachD
  rcases exists_actualDeletionTraceCost_of_reachable
      P hPrimitive hReduced u E hReachE with
    ⟨d, Td⟩
  have hc :
      c = deletionCost P hPrimitive hReduced u D R S :=
    ActualDeletionTraceCost.eq_endpoint_deletionCost
      P hPrimitive hReduced u D T
  have hd :
      d = deletionCost P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) :=
    ActualDeletionTraceCost.eq_endpoint_deletionCost
      P hPrimitive hReduced u E Td
  have hCost :
      deletionCost P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S) =
        deletionCost P hPrimitive hReduced u D R S :=
    deletionCost_transport P hPrimitive hReduced u D E R S
  have hdc : d = c := by
    exact hd.trans (hCost.trans hc.symm)
  rw [hdc] at Td
  exact Td

/-- cost 付き trace relation 自体が decomposition-independent。 -/
theorem actualDeletionTraceCost_transport_iff
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    {c : ℕ} :
    ActualDeletionTraceCost
        P hPrimitive hReduced u E
        (transportRetainedBoundaryPattern D E R)
        (transportRetainedBoundaryPattern D E S) c ↔
      ActualDeletionTraceCost
        P hPrimitive hReduced u D R S c := by
  constructor
  · intro T
    have T' := actualDeletionTraceCost_transport
      P hPrimitive hReduced u E D T
    rw [
      transportRetainedBoundaryPattern_roundtrip D E R,
      transportRetainedBoundaryPattern_roundtrip D E S
    ] at T'
    exact T'
  · intro T
    exact actualDeletionTraceCost_transport
      P hPrimitive hReduced u D E T

/-! ## 7. closure package -/

/--
二つの decomposition の間で canonical Boolean family 全体が保たれることをまとめる。

これは単なる pattern cardinality の一致ではなく、
Boolean algebra、Ferrers geometry、genuine affine cocycle、actual reachability、
cost trace まで同じ system であることを表す。
-/
structure CanonicalBooleanFamilyTransportClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) : Prop where
  pattern_bijective :
    Function.Bijective (transportRetainedBoundaryPattern D E)
  all_exact :
    transportRetainedBoundaryPattern D E (retainAllBoundaries D) =
      retainAllBoundaries E
  none_exact :
    transportRetainedBoundaryPattern D E (retainNoBoundaries D) =
      retainNoBoundaries E
  meet_exact :
    ∀ R S : RetainedBoundaryPattern D,
      transportRetainedBoundaryPattern D E (retainedMeet R S) =
        retainedMeet
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S)
  join_exact :
    ∀ R S : RetainedBoundaryPattern D,
      transportRetainedBoundaryPattern D E (retainedJoin R S) =
        retainedJoin
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S)
  complement_exact :
    ∀ R : RetainedBoundaryPattern D,
      transportRetainedBoundaryPattern D E (retainedComplement R) =
        retainedComplement (transportRetainedBoundaryPattern D E R)
  order_exact :
    ∀ R S : RetainedBoundaryPattern D,
      (transportRetainedBoundaryPattern D E R).Le
          (transportRetainedBoundaryPattern D E S) ↔
        R.Le S
  skeleton_exact :
    ∀ R : RetainedBoundaryPattern D,
      coarsenedLengthsFor E (transportRetainedBoundaryPattern D E R) =
        coarsenedLengthsFor D R
  flat_point_exact :
    ∀ R : RetainedBoundaryPattern D,
      canonicalFlatPoint P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R) =
        canonicalFlatPoint P hPrimitive hReduced u D R
  flat_affine_exact :
    ∀ R : RetainedBoundaryPattern D,
      flatAffine P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R) =
        flatAffine P hPrimitive hReduced u D R
  deletion_cost_exact :
    ∀ R S : RetainedBoundaryPattern D,
      deletionCost P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S) =
        deletionCost P hPrimitive hReduced u D R S
  boundary_potential_exact :
    ∀ R : RetainedBoundaryPattern D,
      boundaryPotential P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R) =
        boundaryPotential P hPrimitive hReduced u D R
  reachability_exact :
    ∀ R S : RetainedBoundaryPattern D,
      ActualCanonicalDeletionReachable
          P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S) ↔
        ActualCanonicalDeletionReachable
          P hPrimitive hReduced u D R S
  trace_cost_exact :
    ∀ (R S : RetainedBoundaryPattern D) (c : ℕ),
      ActualDeletionTraceCost
          P hPrimitive hReduced u E
          (transportRetainedBoundaryPattern D E R)
          (transportRetainedBoundaryPattern D E S) c ↔
        ActualDeletionTraceCost
          P hPrimitive hReduced u D R S c

/--
## Boolean family canonicity 主定理

同じ actual source の任意の二 genuine RecordDecomposition は、
同一の canonical Boolean / Ferrers / arithmetic deletion system を記述する。

従って `RecordDecomposition` は system の構造そのものではなく、
canonical source-intrinsic family を表現する witness にすぎない。
-/
theorem canonicalBooleanFamily_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    CanonicalBooleanFamilyTransportClosed
      P hPrimitive hReduced u D E := by
  refine {
    pattern_bijective := (retainedBoundaryPatternEquiv D E).bijective
    all_exact := transportRetainedBoundaryPattern_all D E
    none_exact := transportRetainedBoundaryPattern_none D E
    meet_exact := ?_
    join_exact := ?_
    complement_exact := ?_
    order_exact := ?_
    skeleton_exact := ?_
    flat_point_exact := ?_
    flat_affine_exact := ?_
    deletion_cost_exact := ?_
    boundary_potential_exact := ?_
    reachability_exact := ?_
    trace_cost_exact := ?_
  }
  · intro R S
    exact transportRetainedBoundaryPattern_meet D E R S
  · intro R S
    exact transportRetainedBoundaryPattern_join D E R S
  · intro R
    exact transportRetainedBoundaryPattern_complement D E R
  · intro R S
    exact transportRetainedBoundaryPattern_le_iff D E R S
  · intro R
    exact coarsenedLengthsFor_transport D E R
  · intro R
    exact canonicalFlatPoint_transport
      P hPrimitive hReduced u D E R
  · intro R
    exact flatAffine_transport
      P hPrimitive hReduced u D E R
  · intro R S
    exact deletionCost_transport
      P hPrimitive hReduced u D E R S
  · intro R
    exact boundaryPotential_transport
      P hPrimitive hReduced u D E R
  · intro R S
    exact actualCanonicalDeletionReachable_transport_iff
      P hPrimitive hReduced u D E R S
  · intro R S c
    exact actualDeletionTraceCost_transport_iff
      P hPrimitive hReduced u D E

end RecordFerrers
end Collatz2
