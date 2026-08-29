import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationFiberDeletionActualCompatibility

/-!
# Record–Ferrers Perturbation / Mixed Move Coherence

`BoundaryDecorationInterfiberMergeCoherence` では boundary merge 同士の coherence、
`ProductDecorationDeletionSystem` / `BoundaryDecorationFiberDeletionActualCompatibility` では
fixed boundary fiber 内の local one-cell deletion と actual Ferrers geometry の compatibility を閉じた。

本ファイルでは残る mixed critical pair

  local one-cell deletion  vs.  canonical boundary merge

を閉じる。

中心となる法則は単純な可換則ではない。
canonical boundary merge は merge される group の decoration 情報を捨て、
merged factor を flat area `0` に置換するため、local edge は

* merge の外側なら target fiber でも one-cell edge として残る。
* merge に吸収される factor 内なら両 endpoint が同じ target へ潰れる。

従って canonical boundary merge は local one-cell graph に対して

  edge -> edge or point

となる。

この事実をまず `LocalAreaTuple` 上の pure product law として示し、
その後 `BoundaryDecorationFiber`、actual boundary fiber、whole Ferrers unit cover へ順に持ち上げる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. LocalAreaTuple 上の intrinsic one-cell relation -/

/--
local-area product 上の one-cell relation。

各 realizable area value は `chooseDecoration` により unique な genuine local decoration を持つ。
relation は、その decoded local decorations のうち exactly one factor だけが
`LocalDecorationCellDeletion` で一段下がる asynchronous product relationとして定義する。
-/
inductive LocalAreaTupleCellDeletion :
    {rs : List ℕ} ->
      LocalAreaTuple rs ->
      LocalAreaTuple rs ->
      Prop
  | head
      {r : ℕ}
      {rs : List ℕ}
      {a b : LocalAreaValue r}
      (T : LocalAreaTuple rs)
      (hAB : LocalDecorationCellDeletion
        a.chooseDecoration b.chooseDecoration) :
      LocalAreaTupleCellDeletion
        (LocalAreaTuple.cons a T)
        (LocalAreaTuple.cons b T)
  | tail
      {r : ℕ}
      {rs : List ℕ}
      (a : LocalAreaValue r)
      {T U : LocalAreaTuple rs}
      (hTU : LocalAreaTupleCellDeletion T U) :
      LocalAreaTupleCellDeletion
        (LocalAreaTuple.cons a T)
        (LocalAreaTuple.cons a U)

namespace LocalAreaTupleCellDeletion

/-- area-product one-cell relation を decoded local-decoration tuple relation へ送る。 -/
theorem toDecorationTuple
    {rs : List ℕ}
    {A B : LocalAreaTuple rs}
    (h : LocalAreaTupleCellDeletion A B) :
    LocalDecorationTupleCellDeletion
      A.toLocalDecorationTuple
      B.toLocalDecorationTuple := by
  induction h with
  | @head r rs a b T hAB =>
      exact LocalDecorationTupleCellDeletion.head
        T.toLocalDecorationTuple hAB
  | @tail r rs a T U hTU ih =>
      exact LocalDecorationTupleCellDeletion.tail
        a.chooseDecoration ih

/-- decoded local-decoration one-cell relation を area-product relation へ送る。 -/
theorem ofDecorationTuple
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion A B) :
    LocalAreaTupleCellDeletion
      A.toLocalAreaTuple
      B.toLocalAreaTuple := by
  induction h with
  | @head r rs A B T hAB =>
      apply LocalAreaTupleCellDeletion.head
      simpa using hAB
  | @tail r rs A T U hTU ih =>
      exact LocalAreaTupleCellDeletion.tail A.toAreaValue ih

/--
area tuple 上の intrinsic one-cell relation と、decoded decoration tuple 上の
既存 product relation は exact に同値。
-/
theorem iff_decorationTuple
    {rs : List ℕ}
    (A B : LocalAreaTuple rs) :
    LocalAreaTupleCellDeletion A B ↔
      LocalDecorationTupleCellDeletion
        A.toLocalDecorationTuple
        B.toLocalDecorationTuple := by
  constructor
  · exact fun h => h.toDecorationTuple
  · intro h
    have hArea := ofDecorationTuple h
    simpa only [LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple] using hArea

/-- index equality に沿った dependent cast は one-cell relation を保存する。 -/
theorem cast
    {rs ss : List ℕ}
    (h : rs = ss)
    {A B : LocalAreaTuple rs}
    (hAB : LocalAreaTupleCellDeletion A B) :
    LocalAreaTupleCellDeletion
      (LocalAreaTuple.cast h A)
      (LocalAreaTuple.cast h B) := by
  subst ss
  exact hAB

/-- dependent cast 後の one-cell relation は元 relation と exact に同値。 -/
theorem cast_iff
    {rs ss : List ℕ}
    (h : rs = ss)
    (A B : LocalAreaTuple rs) :
    LocalAreaTupleCellDeletion
        (LocalAreaTuple.cast h A)
        (LocalAreaTuple.cast h B) ↔
      LocalAreaTupleCellDeletion A B := by
  subst ss
  rfl

end LocalAreaTupleCellDeletion

/-! ## 2. mergeHeadFlat は local edge を保存するか吸収する -/

namespace LocalAreaTuple

/--
`mergeHeadFlat` は source head factor を flat merged factor に置換する。
従って input one-cell edge が head factor にある場合は両 endpoint を同一点へ潰し、
tail にある場合は同じ one-cell edge をそのまま保存する。
-/
theorem mergeHeadFlat_map_cellDeletion
    (r : ℕ)
    (hr : 0 < r)
    {xs : List ℕ}
    (hPos : ∀ x ∈ xs, 0 < x)
    {A B : LocalAreaTuple xs}
    (hAB : LocalAreaTupleCellDeletion A B) :
    mergeHeadFlat r hr xs hPos A =
        mergeHeadFlat r hr xs hPos B ∨
      LocalAreaTupleCellDeletion
        (mergeHeadFlat r hr xs hPos A)
        (mergeHeadFlat r hr xs hPos B) := by
  cases hAB with
  | @head x tail a b T hLocal =>
      left
      rfl
  | @tail x tail a T U hTU =>
      right
      exact LocalAreaTupleCellDeletion.tail
        (flatAreaValue (r + x) (by
          have hx : 0 < x := hPos x (by simp)
          omega))
        hTU

/--
**## Pure Mixed-Move Law for Arbitrary Canonical Coarsening**

任意の Bool coarsening は local-area product の one-cell edge を

  edge -> edge or point

として送る。

`true` branch では head factor を保存する。
`false` branch では tail を先に coarse 化した後 `mergeHeadFlat` を行うため、
changed factor が merged head に来れば吸収され、それより右なら edge として残る。
-/
theorem canonicalCoarsen_map_cellDeletion
    {rs : List ℕ}
    (hPos : ∀ r ∈ rs, 0 < r)
    (flags : List Bool)
    {A B : LocalAreaTuple rs}
    (hAB : LocalAreaTupleCellDeletion A B) :
    canonicalCoarsen rs hPos flags A =
        canonicalCoarsen rs hPos flags B ∨
      LocalAreaTupleCellDeletion
        (canonicalCoarsen rs hPos flags A)
        (canonicalCoarsen rs hPos flags B) := by
  revert flags hPos
  induction hAB with
  /-
  changed factor が現在の head。
  canonicalCoarsen が tuple の第2 factor まで pattern match するので、
  tail tuple T も constructor まで分解してから branch を読む。
  -/
  | @head r rs a b T hLocal =>
      intro hPos flags
      cases rs with
      /- skeleton は [r]。T : LocalAreaTuple [] なので T = nil。 -/
      | nil =>
          cases T
          right
          simp only [canonicalCoarsen]
          exact
            LocalAreaTupleCellDeletion.head
              LocalAreaTuple.nil hLocal
      /- skeleton は r :: s :: tail。T の先頭を露出させる。 -/
      | cons s tail =>
          cases T with
          | cons c C =>
              let hTailPos :
                  ∀ x ∈ s :: tail, 0 < x := by
                intro x hx
                exact hPos x (by simp [hx])
              cases flags with
              /- flags = [] なら canonicalCoarsen は identity。 -/
              | nil =>
                  right
                  exact
                    LocalAreaTupleCellDeletion.head
                      (LocalAreaTuple.cons c C)
                      hLocal
              | cons keep more =>
                  cases keep with
                  /-
                  true:
                  head factor a / b をそのまま残すので、
                  head にあった one-cell edge もそのまま残る。
                  -/
                  | true =>
                      right
                      change
                        LocalAreaTupleCellDeletion
                          (LocalAreaTuple.cons a
                            (canonicalCoarsen
                              (s :: tail)
                              hTailPos
                              more
                              (LocalAreaTuple.cons c C)))
                          (LocalAreaTuple.cons b
                            (canonicalCoarsen
                              (s :: tail)
                              hTailPos
                              more
                              (LocalAreaTuple.cons c C)))
                      exact
                        LocalAreaTupleCellDeletion.head
                          (canonicalCoarsen
                            (s :: tail)
                            hTailPos
                            more
                            (LocalAreaTuple.cons c C))
                          hLocal
                  /-
                  false:
                  head factor a / b はどちらも捨てられ、
                  同じ tail coarse result との flat merge になる。
                  従って両 endpoint は完全に一致する。
                  -/
                  | false =>
                      left
                      rfl
  /-
  changed factor が tail のどこか。
  T, U の先頭 constructor を露出させれば、
  canonicalCoarsen の true/false 定義式が直接簡約できる。
  -/
  | @tail r rs a T U hTU ih =>
      intro hPos flags
      cases rs with
      /-
      T,U : LocalAreaTuple [] なのに hTU があることは不可能。
      -/
      | nil =>
          cases hTU
      | cons s tail =>
          cases T with
          | cons b Tb =>
              cases U with
              | cons c Ub =>
                  let hTailPos :
                      ∀ x ∈ s :: tail, 0 < x := by
                    intro x hx
                    exact hPos x (by simp [hx])
                  cases flags with
                  /- coarsening なし。元の tail edge をそのまま持ち上げる。 -/
                  | nil =>
                      right
                      exact
                        LocalAreaTupleCellDeletion.tail a hTU
                  | cons keep more =>
                      have hRec :=
                        ih hTailPos more
                      cases keep with
                      /-
                      true:
                      head a は保存される。
                      recursive tail が point なら全体も point、
                      edge なら cons a で edge を持ち上げる。
                      -/
                      | true =>
                          rcases hRec with hEq | hStep
                          · left
                            change
                              LocalAreaTuple.cons a
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons b Tb)) =
                                LocalAreaTuple.cons a
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons c Ub))
                            rw [hEq]
                          · right
                            change
                              LocalAreaTupleCellDeletion
                                (LocalAreaTuple.cons a
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons b Tb)))
                                (LocalAreaTuple.cons a
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons c Ub)))
                            exact
                              LocalAreaTupleCellDeletion.tail
                                a hStep
                      /-
                      false:
                      recursive tail result に mergeHeadFlat を適用する。

                      recursive edge が既に point なら merge 後も point。
                      recursive edge が残っていれば
                      mergeHeadFlat_map_cellDeletion により
                      再び edge or point。
                      -/
                      | false =>
                          rcases hRec with hEq | hStep
                          · left
                            change
                              mergeHeadFlat
                                  r
                                  (hPos r (by simp))
                                  (coarsenByFlags
                                    (s :: tail) more)
                                  (coarsenByFlags_all_pos
                                    more hTailPos)
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons b Tb)) =
                                mergeHeadFlat
                                  r
                                  (hPos r (by simp))
                                  (coarsenByFlags
                                    (s :: tail) more)
                                  (coarsenByFlags_all_pos
                                    more hTailPos)
                                  (canonicalCoarsen
                                    (s :: tail)
                                    hTailPos
                                    more
                                    (LocalAreaTuple.cons c Ub))
                            rw [hEq]
                          · change
                              mergeHeadFlat
                                    r
                                    (hPos r (by simp))
                                    (coarsenByFlags
                                      (s :: tail) more)
                                    (coarsenByFlags_all_pos
                                      more hTailPos)
                                    (canonicalCoarsen
                                      (s :: tail)
                                      hTailPos
                                      more
                                      (LocalAreaTuple.cons b Tb)) =
                                  mergeHeadFlat
                                    r
                                    (hPos r (by simp))
                                    (coarsenByFlags
                                      (s :: tail) more)
                                    (coarsenByFlags_all_pos
                                      more hTailPos)
                                    (canonicalCoarsen
                                      (s :: tail)
                                      hTailPos
                                      more
                                      (LocalAreaTuple.cons c Ub)) ∨
                                LocalAreaTupleCellDeletion
                                  (mergeHeadFlat
                                    r
                                    (hPos r (by simp))
                                    (coarsenByFlags
                                      (s :: tail) more)
                                    (coarsenByFlags_all_pos
                                      more hTailPos)
                                    (canonicalCoarsen
                                      (s :: tail)
                                      hTailPos
                                      more
                                      (LocalAreaTuple.cons b Tb)))
                                  (mergeHeadFlat
                                    r
                                    (hPos r (by simp))
                                    (coarsenByFlags
                                      (s :: tail) more)
                                    (coarsenByFlags_all_pos
                                      more hTailPos)
                                    (canonicalCoarsen
                                      (s :: tail)
                                      hTailPos
                                      more
                                      (LocalAreaTuple.cons c Ub)))
                            exact
                              mergeHeadFlat_map_cellDeletion
                                r
                                (hPos r (by simp))
                                (coarsenByFlags_all_pos
                                  more hTailPos)
                                hStep

end LocalAreaTuple

/-! ## 3. BoundaryDecorationFiberCellDeletion の pure coordinate characterization -/

/--
boundary fiber equivalence の inverse で actual source に戻した後に抽出される
local-area tuple は、boundary index cast を逆向きに施した abstract coordinateそのもの。
-/
theorem boundaryDecorationFiberEquiv_symm_fixedSkeletonLocalAreaTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A : BoundaryDecorationFiber D R) :
    fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R)
        ((boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R).symm A) =
      LocalAreaTuple.cast
        (boundaryCanonicalDecomposition_lengths
          P hPrimitive hReduced u D R).symm A := by
  let hLen :=
    boundaryCanonicalDecomposition_lengths
      P hPrimitive hReduced u D R
  let e :=
    boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R
  let X := e.symm A
  apply (LocalAreaTuple.castEquiv hLen).injective
  change
    e X =
      (LocalAreaTuple.castEquiv hLen)
        ((LocalAreaTuple.castEquiv hLen).symm A)
  rw [e.apply_symm_apply]
  exact
    ((LocalAreaTuple.castEquiv hLen).apply_symm_apply A).symm

/--
boundary fiber coordinate の inverse realization が抽出する concrete local-decoration tuple。
-/
theorem boundaryDecorationFiberEquiv_symm_toLocalDecorationTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A : BoundaryDecorationFiber D R) :
    ((boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R).symm A).toLocalDecorationTuple =
      (LocalAreaTuple.cast
        (boundaryCanonicalDecomposition_lengths
          P hPrimitive hReduced u D R).symm A).toLocalDecorationTuple := by
  let X :=
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm A
  let E :=
    boundaryCanonicalDecomposition
      P hPrimitive hReduced u D R
  let hLen :=
    boundaryCanonicalDecomposition_lengths
      P hPrimitive hReduced u D R
  have hArea :=
    boundaryDecorationFiberEquiv_symm_fixedSkeletonLocalAreaTuple
      P hPrimitive hReduced u D R A
  have hFixed :=
    fixedSkeletonLocalAreaTuple_eq
      P hPrimitive hReduced
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      E X
  apply (localDecorationTupleEquivAreaTuple E.lengths).injective
  change
    X.toLocalDecorationTuple.toLocalAreaTuple =
      (LocalAreaTuple.cast hLen.symm A).toLocalDecorationTuple.toLocalAreaTuple
  rw [LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple]
  rw [← hFixed]
  exact hArea

/--
## Boundary Fiber One-Cell Coordinate Characterization

既存 `BoundaryDecorationFiberCellDeletion` は、abstract local-area product 上の
`LocalAreaTupleCellDeletion` そのもの。

従って fiber-local rewrite は primitive/reduced actual realization を忘れた pure product relation として読める。
-/
theorem boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A B : BoundaryDecorationFiber D R) :
    BoundaryDecorationFiberCellDeletion
        P hPrimitive hReduced u D R A B ↔
      LocalAreaTupleCellDeletion A B := by
  unfold BoundaryDecorationFiberCellDeletion
  unfold BoundaryDecorationActualFiberProductCellDeletion
  unfold FixedSkeletonProductCellDeletion
  rw [
    boundaryDecorationFiberEquiv_symm_toLocalDecorationTuple
      P hPrimitive hReduced u D R A,
    boundaryDecorationFiberEquiv_symm_toLocalDecorationTuple
      P hPrimitive hReduced u D R B
  ]
  rw [← LocalAreaTupleCellDeletion.iff_decorationTuple]
  exact LocalAreaTupleCellDeletion.cast_iff
    (boundaryCanonicalDecomposition_lengths
      P hPrimitive hReduced u D R).symm A B

/-! ## 4. canonical inter-fiber map は local edge を edge or point へ送る -/

/--
任意 `S ≤ R` の canonical abstract coarsening は fiber-local one-cell edge を
同一点へ吸収するか、target fiber の one-cell edge として保存する。
-/
theorem boundaryDecorationCanonicalInterfiberCoarsening_map_areaCellDeletion
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R)
    {A B : BoundaryDecorationFiber D R}
    (hAB : LocalAreaTupleCellDeletion A B) :
    boundaryDecorationCanonicalInterfiberCoarsening D hSR A =
        boundaryDecorationCanonicalInterfiberCoarsening D hSR B ∨
      LocalAreaTupleCellDeletion
        (boundaryDecorationCanonicalInterfiberCoarsening D hSR A)
        (boundaryDecorationCanonicalInterfiberCoarsening D hSR B) := by
  unfold boundaryDecorationCanonicalInterfiberCoarsening
  let hIdx := (relativeBoundaryFlags_spec D hSR).2
  have hCore :=
    LocalAreaTuple.canonicalCoarsen_map_cellDeletion
      (coarsenedLengthsFor_pos D R)
      (relativeBoundaryFlags R S)
      hAB
  rcases hCore with hEq | hStep
  · left
    exact congrArg (LocalAreaTuple.cast hIdx) hEq
  · right
    exact LocalAreaTupleCellDeletion.cast hIdx hStep

/-- one-boundary canonical merge specialization。 -/
theorem boundaryDecorationCanonicalInterfiberMerge_map_areaCellDeletion
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    {A B : BoundaryDecorationFiber D R}
    (hAB : LocalAreaTupleCellDeletion A B) :
    boundaryDecorationCanonicalInterfiberMerge D R b A =
        boundaryDecorationCanonicalInterfiberMerge D R b B ∨
      LocalAreaTupleCellDeletion
        (boundaryDecorationCanonicalInterfiberMerge D R b A)
        (boundaryDecorationCanonicalInterfiberMerge D R b B) := by
  exact boundaryDecorationCanonicalInterfiberCoarsening_map_areaCellDeletion
    D (eraseRetainedBoundary_le R b) hAB

/--
## Abstract Mixed-Move Coherence

boundary fiber の genuine local one-cell edge に one-boundary canonical merge を作用させると、
その edge は target fiber の genuine local edge として残るか、merge に吸収されて endpoint が一致する。
-/
theorem boundaryDecorationCanonicalInterfiberMerge_map_cellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    {A B : BoundaryDecorationFiber D R}
    (hAB : BoundaryDecorationFiberCellDeletion
      P hPrimitive hReduced u D R A B) :
    boundaryDecorationCanonicalInterfiberMerge D R b A =
        boundaryDecorationCanonicalInterfiberMerge D R b B ∨
      BoundaryDecorationFiberCellDeletion
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationCanonicalInterfiberMerge D R b A)
        (boundaryDecorationCanonicalInterfiberMerge D R b B) := by
  have hArea : LocalAreaTupleCellDeletion A B :=
    (boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
      P hPrimitive hReduced u D R A B).1 hAB
  rcases
      boundaryDecorationCanonicalInterfiberMerge_map_areaCellDeletion
        D R b hArea with hEq | hStep
  · exact Or.inl hEq
  · exact Or.inr
      ((boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationCanonicalInterfiberMerge D R b A)
        (boundaryDecorationCanonicalInterfiberMerge D R b B)).2 hStep)

/-! ## 5. actual boundary fiber への lift -/

/-- actual product step と abstract fiber coordinates 上の one-cell relation は exact に同値。 -/
theorem boundaryDecorationActualFiberProductCellDeletion_iff_coordinates
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    BoundaryDecorationActualFiberProductCellDeletion
        P hPrimitive hReduced u D R X Y ↔
      BoundaryDecorationFiberCellDeletion
        P hPrimitive hReduced u D R
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X)
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R Y) := by
  unfold BoundaryDecorationFiberCellDeletion
  unfold BoundaryDecorationActualFiberProductCellDeletion
  rw [
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm_apply_apply,
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm_apply_apply
  ]

/--
## Actual Mixed-Move Coherence

actual boundary fiber の product one-cell edgeを genuine one-boundary canonical merge に通すと、
target actual states は一致するか、target fiber 内の product one-cell edgeとして残る。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_map_productCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    {X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R}
    (hXY : BoundaryDecorationActualFiberProductCellDeletion
      P hPrimitive hReduced u D R X Y) :
    boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X =
        boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y ∨
      BoundaryDecorationActualFiberProductCellDeletion
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y) := by
  let eR := boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D R
  let S := eraseRetainedBoundary R b
  let eS := boundaryDecorationFiberEquiv
    P hPrimitive hReduced u D S
  let MX := boundaryDecorationActualCanonicalInterfiberMerge
    P hPrimitive hReduced u D R b X
  let MY := boundaryDecorationActualCanonicalInterfiberMerge
    P hPrimitive hReduced u D R b Y
  have hCoordXY :
      BoundaryDecorationFiberCellDeletion
        P hPrimitive hReduced u D R (eR X) (eR Y) :=
    (boundaryDecorationActualFiberProductCellDeletion_iff_coordinates
      P hPrimitive hReduced u D R X Y).1 hXY
  have hMixed :=
    boundaryDecorationCanonicalInterfiberMerge_map_cellDeletion
      P hPrimitive hReduced u D R b hCoordXY
  rcases hMixed with hEq | hStep
  · left
    apply eS.injective
    dsimp [MX, MY, eS, S]
    rw [
      boundaryDecorationActualCanonicalInterfiberMerge_coordinate,
      boundaryDecorationActualCanonicalInterfiberMerge_coordinate
    ]
    exact hEq
  · right
    apply
      (boundaryDecorationActualFiberProductCellDeletion_iff_coordinates
        P hPrimitive hReduced u D S MX MY).2
    dsimp [MX, MY, eS, S]
    rw [
      boundaryDecorationActualCanonicalInterfiberMerge_coordinate,
      boundaryDecorationActualCanonicalInterfiberMerge_coordinate
    ]
    exact hStep

/--
actual mixed law を whole Ferrers geometry で読む。
merge 後 endpoint が異なる場合、その二点は genuine `FerrersShape.IsUnitCover` で結ばれる。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_map_unitCover_or_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    {X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R}
    (hXY : BoundaryDecorationActualFiberProductCellDeletion
      P hPrimitive hReduced u D R X Y) :
    boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X =
        boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y ∨
      FerrersShape.IsUnitCover
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y).1.toFerrersShape
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1.toFerrersShape := by
  rcases
      boundaryDecorationActualCanonicalInterfiberMerge_map_productCellDeletion
        P hPrimitive hReduced u D R b hXY with hEq | hStep
  · exact Or.inl hEq
  · exact Or.inr
      (boundaryDecorationActualFiberProductCellDeletion_to_actual
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b) hStep)

/-! ## 6. genuine boundary deletion specialization と closure -/

/--
retained boundary `b` の genuine deletion に対する mixed diamond。
`hb` は genuine boundary move であることの guard であり、edge-or-point law 自体はより一般に成立する。
-/
theorem boundaryDecoration_genuineMerge_localDeletion_diamond
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (_hb : R b = true)
    {X Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R}
    (hXY : BoundaryDecorationActualFiberProductCellDeletion
      P hPrimitive hReduced u D R X Y) :
    boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X =
        boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y ∨
      BoundaryDecorationActualFiberProductCellDeletion
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X)
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b Y) :=
  boundaryDecorationActualCanonicalInterfiberMerge_map_productCellDeletion
    P hPrimitive hReduced u D R b hXY

/-- mixed move coherence layer で閉じた内容。 -/
structure BoundaryDecorationMixedMoveCoherenceClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  abstract_edge_or_point :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D)
      (A B : BoundaryDecorationFiber D R),
      BoundaryDecorationFiberCellDeletion
          P hPrimitive hReduced u D R A B ->
        boundaryDecorationCanonicalInterfiberMerge D R b A =
            boundaryDecorationCanonicalInterfiberMerge D R b B ∨
          BoundaryDecorationFiberCellDeletion
            P hPrimitive hReduced u D
            (eraseRetainedBoundary R b)
            (boundaryDecorationCanonicalInterfiberMerge D R b A)
            (boundaryDecorationCanonicalInterfiberMerge D R b B)

  actual_edge_or_point :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D)
      (X Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      BoundaryDecorationActualFiberProductCellDeletion
          P hPrimitive hReduced u D R X Y ->
        boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b X =
            boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b Y ∨
          BoundaryDecorationActualFiberProductCellDeletion
            P hPrimitive hReduced u D
            (eraseRetainedBoundary R b)
            (boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b X)
            (boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b Y)

  actual_geometric_edge_or_point :
    ∀ (R : RetainedBoundaryPattern D)
      (b : InternalRecordBoundary D)
      (X Y : BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R),
      BoundaryDecorationActualFiberProductCellDeletion
          P hPrimitive hReduced u D R X Y ->
        boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b X =
            boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b Y ∨
          FerrersShape.IsUnitCover
            (boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b Y).1.toFerrersShape
            (boundaryDecorationActualCanonicalInterfiberMerge
              P hPrimitive hReduced u D R b X).1.toFerrersShape

/--
## Mixed Move Coherence Closure

local/local は product deletion system、boundary/boundary は canonical inter-fiber coherence、
local/boundary は本 theorem の edge-or-point law で閉じる。
これにより global normalization に必要な三種類の critical-pair geometry が揃う。
-/
theorem boundaryDecorationMixedMoveCoherence_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationMixedMoveCoherenceClosed
      P hPrimitive hReduced u D := by
  refine {
    abstract_edge_or_point := ?_
    actual_edge_or_point := ?_
    actual_geometric_edge_or_point := ?_
  }
  · intro R b A B hAB
    exact boundaryDecorationCanonicalInterfiberMerge_map_cellDeletion
      P hPrimitive hReduced u D R b hAB
  · intro R b X Y hXY
    exact boundaryDecorationActualCanonicalInterfiberMerge_map_productCellDeletion
      P hPrimitive hReduced u D R b hXY
  · intro R b X Y hXY
    exact boundaryDecorationActualCanonicalInterfiberMerge_map_unitCover_or_eq
      P hPrimitive hReduced u D R b hXY

end RecordFerrers
end Collatz2
