import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ProductDecorationDeletionSystem
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecoratedDeletionSystem

/-!
# Record–Ferrers Perturbation / Boundary Decoration Bundle

`ProductDecorationDeletionSystem` までで、固定した一つの genuine record skeleton 上では
actual state space が local-decoration / local-area の dependent product と exact に同一視され、
その内部 rewrite が one-factor-at-a-time の product deletion system を持つことが分かった。

一方 P29--P35 と `DeletionPotentialCocycle` では、元 decomposition `D` の内部 Record 境界を
保持 / 消去する Boolean base

  R : RetainedBoundaryPattern D

があり、各 `R` は coarse length skeleton

  coarsenedLengthsFor D R

と choice-free canonical flat point を持つ。

本ファイルではこの二つを初めて一つの dependent bundle に束ねる。

  base R
      |
      +-- fiber = LocalAreaTuple (coarsenedLengthsFor D R)

従って bundle は単純な

  Boundary × Decoration

ではない。boundary を消すと record blocks が merge し、fiber の index length list 自体が
変わるため、正しい型は dependent sum である。

さらに各 base `R` の canonical flat point は、その coarse skeleton の genuine
RecordDecomposition を持つ。これを anchor に fixed-skeleton area-product equivalence を適用し、
各 abstract fiber が actual sources の fiber と exact に同値であることまで閉じる。

算術量としては、base `R` から absolute bottom まで「まだ残っている」boundary cost

  deletionCost R none

と fiber weighted area を足して

  remaining boundary cost + 2 * local weighted area

を bundle total excess とする。元 source を top fiber に埋め込むと、これは既存の
`arithmeticDecoratedTotalExcess` と exact に一致する。

重要な分離:
本ファイルでは flat section 上の boundary deletion と、各 fixed base fiber 内の product
normalization を同じ bundle に載せる。ただし boundary deletion に伴って arbitrary decorated
fiber point を別 skeleton fiber へ送る merge map はまだ定義しない。その inter-fiber transport は
この bundle 構造を得た後の独立な問題として残す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. coarse skeleton の positivity -/

/-- genuine positive record lengths は Boolean coarsening 後も全成分 positive。 -/
theorem coarsenedLengthsFor_pos
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ∀ r ∈ coarsenedLengthsFor D R, 0 < r := by
  unfold coarsenedLengthsFor
  exact coarsenByFlags_all_pos (retainedFlags R) D.lengths_pos

/-! ## 2. LocalAreaTuple の index transport -/

namespace LocalAreaTuple

/-- length-list equality に沿って dependent local-area tuple を transport する。 -/
def cast
    {rs ss : List ℕ}
    (h : rs = ss)
    (A : LocalAreaTuple rs) : LocalAreaTuple ss := by
  subst ss
  exact A

@[simp] theorem cast_rfl
    {rs : List ℕ}
    (A : LocalAreaTuple rs) :
    cast rfl A = A := rfl

/-- index transport は weighted-area potential を変えない。 -/
theorem cast_weightedArea
    {rs ss : List ℕ}
    (h : rs = ss)
    (A : LocalAreaTuple rs) :
    (cast h A).weightedArea = A.weightedArea := by
  subst ss
  rfl

/-- length-list equality に沿った exact equivalence。 -/
def castEquiv
    {rs ss : List ℕ}
    (h : rs = ss) :
    LocalAreaTuple rs ≃ LocalAreaTuple ss where
  toFun := cast h
  invFun := cast h.symm
  left_inv := by
    subst ss
    intro A
    rfl
  right_inv := by
    subst ss
    intro A
    rfl

end LocalAreaTuple

/-! ## 3. 各 boundary pattern の canonical actual fiber -/

/--
pattern `R` の canonical flat point が持つ coarse RecordDecomposition を一つ選ぶ。
存在は P30 の choice-free flat representative theorem による。

choice は decomposition proof-object のみに使い、underlying canonical flat FiberPoint 自体は
choice-free である。
-/
noncomputable def boundaryCanonicalDecomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    RecordDecomposition
      (canonicalFlatPoint P hPrimitive hReduced u D R) 1 := by
  change RecordDecomposition
    (canonicalFlatRepresentative P hPrimitive hReduced u D R) 1
  exact Classical.choose
    (exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D R)

/-- selected canonical decomposition の lengths は pattern の coarse skeleton と exact に一致。 -/
theorem boundaryCanonicalDecomposition_lengths
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    (boundaryCanonicalDecomposition
      P hPrimitive hReduced u D R).lengths =
      coarsenedLengthsFor D R := by
  change
    (Classical.choose
      (exists_canonicalFlatRecordDecomposition
        P hPrimitive hReduced u D R)).lengths =
      coarsenedLengthsFor D R
  exact Classical.choose_spec
    (exists_canonicalFlatRecordDecomposition
      P hPrimitive hReduced u D R)

/-- pattern `R` 上の abstract local-area fiber。 -/
def BoundaryDecorationFiber
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : Type :=
  LocalAreaTuple (coarsenedLengthsFor D R)

/--
pattern `R` の canonical flat point を anchor とし、その coarse skeleton を固定した actual source fiber。
-/
def BoundaryDecorationActualFiber
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : Type :=
  FixedSkeletonSource
    P
    (canonicalFlatPoint P hPrimitive hReduced u D R)
    (boundaryCanonicalDecomposition
      P hPrimitive hReduced u D R)

/--
## Fiber Equivalence

各 Boolean base `R` の actual same-skeleton source fiber は、coarsened length list 上の
local-area product と exact に同値。
-/
noncomputable def boundaryDecorationFiberEquiv
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    BoundaryDecorationActualFiber
        P hPrimitive hReduced u D R ≃
      BoundaryDecorationFiber D R :=
  (fixedSkeletonSourceEquivLocalAreaProduct
      P hPrimitive hReduced
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (boundaryCanonicalDecomposition
        P hPrimitive hReduced u D R)).trans
    (LocalAreaTuple.castEquiv
      (boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D R))

/-- fiber equivalence の index cast は weighted area を変えない。 -/
theorem boundaryDecorationFiberEquiv_weightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R X).weightedArea =
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R)
        X).weightedArea := by
  change
    (LocalAreaTuple.cast
      (boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D R)
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R)
        X)).weightedArea =
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R)
        X).weightedArea
  exact LocalAreaTuple.cast_weightedArea _ _

/-! ## 4. dependent bundle と actual bundle -/

/--
Boolean boundary base 上に coarse local-area product fibers を載せた dependent bundle。

これは `Σ R, LocalAreaTuple (coarsenedLengthsFor D R)` そのもの。
-/
def BoundaryDecorationBundle
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : Type :=
  Σ R : RetainedBoundaryPattern D, BoundaryDecorationFiber D R

/-- 各 base の actual same-skeleton source fibers を束ねた actual bundle。 -/
def BoundaryDecorationActualBundle
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Type :=
  Σ R : RetainedBoundaryPattern D,
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R

/--
## Boundary Decoration Bundle Equivalence

actual bundle と abstract local-area bundle は base pattern を固定したまま fiberwise exact に同値。
-/
noncomputable def boundaryDecorationBundleEquiv
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationActualBundle
        P hPrimitive hReduced u D ≃
      BoundaryDecorationBundle D where
  toFun := fun Z =>
    ⟨Z.1,
      boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D Z.1 Z.2⟩
  invFun := fun Z =>
    ⟨Z.1,
      (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D Z.1).symm Z.2⟩
  left_inv := by
    intro Z
    rcases Z with ⟨R, X⟩
    change
      Sigma.mk R
          ((boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R).symm
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X)) =
        Sigma.mk R X
    rw [(boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm_apply_apply]
  right_inv := by
    intro Z
    rcases Z with ⟨R, A⟩
    change
      Sigma.mk R
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R
            ((boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R).symm A)) =
        Sigma.mk R A
    rw [(boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).apply_symm_apply]

/-! ## 5. bundle の flat section -/

/-- canonical flat local factor の local decoration area は 0。 -/
theorem localDecorationArea_localFlatDecoration_eq_zero
    (r : ℕ)
    (hr : 0 < r) :
    localDecorationArea (localFlatDecoration r hr).word = 0 := by
  unfold localDecorationArea
  rw [localFlatDecoration_affineConst r hr]
  rw [(localFlatDecoration r hr).length_eq]
  simp

/-- all-flat product tuple の skeleton-weighted area は 0。 -/
theorem flatLocalDecorationTuple_weightedArea_eq_zero
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r) :
    (flatLocalDecorationTuple rs hPos).weightedArea = 0 := by
  induction rs with
  | nil =>
      rfl
  | cons r rs ih =>
      let hr : 0 < r := hPos r (by simp)
      let hTailPos : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hPos s (by simp [hs])
      change
        3 ^ rs.sum *
              localDecorationArea (localFlatDecoration r hr).word +
            2 ^ minimalDepth r *
              (flatLocalDecorationTuple rs hTailPos).weightedArea = 0
      rw [localDecorationArea_localFlatDecoration_eq_zero r hr]
      rw [ih hTailPos]
      simp

/-- base `R` の all-flat area-product point。 -/
def boundaryDecorationFlatFiber
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    BoundaryDecorationFiber D R :=
  (flatLocalDecorationTuple
    (coarsenedLengthsFor D R)
    (coarsenedLengthsFor_pos D R)).toLocalAreaTuple

/-- flat fiber coordinate の weighted area は 0。 -/
theorem boundaryDecorationFlatFiber_weightedArea_eq_zero
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    (boundaryDecorationFlatFiber D R).weightedArea = 0 := by
  change
    ((flatLocalDecorationTuple
        (coarsenedLengthsFor D R)
        (coarsenedLengthsFor_pos D R)).toLocalAreaTuple).weightedArea = 0
  simpa only [
    ← LocalDecorationTuple.weightedArea_eq_toLocalAreaTuple_weightedArea
  ] using
    flatLocalDecorationTuple_weightedArea_eq_zero
      (coarsenedLengthsFor D R)
      (coarsenedLengthsFor_pos D R)

/-- Boolean base 全体に沿った canonical all-flat section。 -/
def boundaryDecorationFlatSection
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    BoundaryDecorationBundle D :=
  ⟨R, boundaryDecorationFlatFiber D R⟩

/-! ## 6. boundary base の remaining potential -/

/--
pattern `R` の canonical flat state から absolute no-boundary bottom までに
まだ残っている boundary arithmetic cost。
-/
def boundaryResidualToBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) : ℕ :=
  deletionCost P hPrimitive hReduced u D
    R (retainNoBoundaries D)

/-- top で remaining boundary residual は既存 `boundaryGap` そのもの。 -/
theorem boundaryResidualToBottom_top_eq_boundaryGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryResidualToBottom
        P hPrimitive hReduced u D (retainAllBoundaries D) =
      boundaryGap P hPrimitive hReduced u D := by
  exact deletionCost_top_bottom_eq_boundaryGap
    P hPrimitive hReduced u D

/-- absolute bottom では remaining boundary residual は 0。 -/
@[simp] theorem boundaryResidualToBottom_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryResidualToBottom
      P hPrimitive hReduced u D (retainNoBoundaries D) = 0 := by
  simp [boundaryResidualToBottom]

/--
`R -> S` の下向き boundary move では、R から bottom までの remaining cost は
edge cost と S から bottom までの remaining cost に exact 分解する。
-/
theorem boundaryResidualToBottom_step
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    boundaryResidualToBottom P hPrimitive hReduced u D R =
      deletionCost P hPrimitive hReduced u D R S +
        boundaryResidualToBottom P hPrimitive hReduced u D S := by
  unfold boundaryResidualToBottom
  exact deletionCost_add_of_retainedLe
    P hPrimitive hReduced u D
    hSR (RetainedBoundaryPattern.none_le D S)

/--
flat affine potential は absolute base + remaining boundary residual に exact 分解する。
-/
theorem flatAffine_eq_absoluteBase_add_boundaryResidualToBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    flatAffine P hPrimitive hReduced u D R =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryResidualToBottom P hPrimitive hReduced u D R := by
  have hNoneLe :
      flatAffine P hPrimitive hReduced u D (retainNoBoundaries D) ≤
        flatAffine P hPrimitive hReduced u D R :=
    flatAffine_mono_of_retainedLe
      P hPrimitive hReduced u D
      (RetainedBoundaryPattern.none_le D R)
  rcases canonicalNoBoundaryPoint_global_potential_minimum
      P hPrimitive hReduced u D with
    ⟨_hArea, hBottom, _hAreaMin, _hAffineMin⟩
  have hNone :
      flatAffine P hPrimitive hReduced u D (retainNoBoundaries D) =
        3 ^ P.oddCount - 2 ^ P.oddCount := by
    simpa [flatAffine, canonicalNoBoundaryPoint] using hBottom
  unfold boundaryResidualToBottom deletionCost
  rw [hNone]
  omega

/-! ## 7. bundle total excess -/

/--
Bundle point `(R,A)` が absolute bottom より上に持つ total arithmetic excess。

base direction の remaining boundary cost と、fiber direction の local-area cost の和。
-/
def boundaryDecorationBundleTotalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) : ℕ :=
  boundaryResidualToBottom P hPrimitive hReduced u D Z.1 +
    2 * Z.2.weightedArea

/-- flat section 上では fiber contribution が消え、total excess は base residual だけ。 -/
theorem boundaryDecorationBundleTotalExcess_flatSection
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D R) =
      boundaryResidualToBottom P hPrimitive hReduced u D R := by
  unfold boundaryDecorationBundleTotalExcess
  simp [
    boundaryDecorationFlatSection,
    boundaryDecorationFlatFiber_weightedArea_eq_zero
  ]

/-- flat section の absolute bottom は bundle total excess の零点。 -/
theorem boundaryDecorationBundleTotalExcess_flatBottom_eq_zero
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D (retainNoBoundaries D)) = 0 := by
  rw [boundaryDecorationBundleTotalExcess_flatSection]
  exact boundaryResidualToBottom_bottom
    P hPrimitive hReduced u D

/--
flat section の boundary descent は bundle total excess を edge deletion cost で exact に分解する。
-/
theorem boundaryDecorationBundleTotalExcess_flatSection_step
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hSR : S.Le R) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D R) =
      deletionCost P hPrimitive hReduced u D R S +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (boundaryDecorationFlatSection D S) := by
  rw [
    boundaryDecorationBundleTotalExcess_flatSection,
    boundaryDecorationBundleTotalExcess_flatSection
  ]
  exact boundaryResidualToBottom_step
    P hPrimitive hReduced u D hSR

/-- genuine one-boundary deletion なら flat-section total excess は strict に減る。 -/
theorem boundaryDecorationBundleTotalExcess_strict_of_actualBoundaryDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (A : ActualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D R S) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D S) <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D R) := by
  have hSplit :=
    boundaryDecorationBundleTotalExcess_flatSection_step
      P hPrimitive hReduced u D A.pattern_step.le
  have hCost :=
    deletionCost_pos_of_actualCanonicalBoundaryDeletion
      P hPrimitive hReduced u D A
  omega

/-! ## 8. 元 actual source の top-fiber embedding -/

/--
元 source `u` を all-boundaries base の actual fiber の点として埋め込む。
all-boundaries coarse skeleton は `D.lengths` そのもの。
-/
noncomputable def sourceTopBoundaryDecorationActualFiber
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationActualFiber
      P hPrimitive hReduced u D (retainAllBoundaries D) := by
  refine ⟨u, ?_⟩
  refine ⟨D, ?_⟩
  have hCanonical :=
    boundaryCanonicalDecomposition_lengths
      P hPrimitive hReduced u D (retainAllBoundaries D)
  exact
    (coarsenedLengthsFor_retainAllBoundaries D).symm.trans
      hCanonical.symm

/-- 元 source を abstract boundary-decoration bundle の top fiber へ送る。 -/
noncomputable def sourceBoundaryDecorationBundlePoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundle D :=
  ⟨retainAllBoundaries D,
    boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D
      (retainAllBoundaries D)
      (sourceTopBoundaryDecorationActualFiber
        P hPrimitive hReduced u D)⟩

/-- top embedding の fiber weighted area は既存 local weighted decoration area と exact に一致。 -/
theorem sourceBoundaryDecorationBundlePoint_weightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (sourceBoundaryDecorationBundlePoint
      P hPrimitive hReduced u D).2.weightedArea =
      localWeightedDecorationArea P u D := by
  let R := retainAllBoundaries D
  let E0 := boundaryCanonicalDecomposition
    P hPrimitive hReduced u D R
  let X := sourceTopBoundaryDecorationActualFiber
    P hPrimitive hReduced u D
  have hCast :=
    boundaryDecorationFiberEquiv_weightedArea
      P hPrimitive hReduced u D R X
  have hLengths : D.lengths = E0.lengths := by
    dsimp [E0, R]
    have hCanonical :=
      boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D (retainAllBoundaries D)
    exact
      (coarsenedLengthsFor_retainAllBoundaries D).symm.trans
        hCanonical.symm
  have hRecord :=
    fixedSkeletonLocalAreaTuple_weightedArea_eq_any_decomposition
      P hPrimitive hReduced
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      E0 X D hLengths
  change
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R X).weightedArea =
      localWeightedDecorationArea P u D
  rw [hCast]
  unfold localWeightedDecorationArea
  exact hRecord

/--
## Source Bundle Potential 主定理

元 actual source を top fiber に埋め込んだ bundle total excess は、既存の二段階
`arithmeticDecoratedTotalExcess` と exact に同じ。
-/
theorem sourceBoundaryDecorationBundlePoint_totalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D) =
      arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D := by
  change
    boundaryResidualToBottom
        P hPrimitive hReduced u D (retainAllBoundaries D) +
      2 *
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D).2.weightedArea =
      arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
  rw [boundaryResidualToBottom_top_eq_boundaryGap]
  rw [sourceBoundaryDecorationBundlePoint_weightedArea]
  rfl

/--
元 source の affine constant は absolute base + bundle total excess に exact 分解する。
-/
theorem affineConst_eq_absoluteBase_add_sourceBoundaryDecorationBundleTotalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (sourceBoundaryDecorationBundlePoint
            P hPrimitive hReduced u D) := by
  calc
    affineConst u.word =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          arithmeticDecoratedTotalExcess
            P hPrimitive hReduced u D :=
      affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
    _ =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          boundaryDecorationBundleTotalExcess
            P hPrimitive hReduced u D
            (sourceBoundaryDecorationBundlePoint
              P hPrimitive hReduced u D) := by
      rw [sourceBoundaryDecorationBundlePoint_totalExcess]

/-! ## 9. 各 fiber の product deletion system -/

/--
各 Boolean base の coarse skeleton は、それ自身の terminating / joinable product decoration
system を持つ。
-/
theorem boundaryDecorationFiber_productDeletionSystem_closed
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    ProductDecorationDeletionSystemClosed
      (coarsenedLengthsFor D R)
      (coarsenedLengthsFor_pos D R) :=
  productDecorationDeletionSystem_closed
    (coarsenedLengthsFor D R)
    (coarsenedLengthsFor_pos D R)

/-! ## 10. closure package -/

/--
Boundary Decoration Bundle 層で閉じた構造。

* Boolean base 上の dependent area-product fibers
* 各 fiber と actual same-skeleton sources の exact equivalence
* 各 fiber の terminating / joinable product normalization
* flat section 上の boundary cocycle
* top source の bundle total potential と既存 arithmetic total excess の一致
* absolute bottom flat section の total potential 0

を一つにまとめる。
-/
structure BoundaryDecorationBundleClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  bundle_bijective :
    Function.Bijective
      (boundaryDecorationBundleEquiv
        P hPrimitive hReduced u D)
  coarse_lengths_positive :
    ∀ R : RetainedBoundaryPattern D,
      ∀ r ∈ coarsenedLengthsFor D R, 0 < r
  fiber_product_system :
    ∀ R : RetainedBoundaryPattern D,
      ProductDecorationDeletionSystemClosed
        (coarsenedLengthsFor D R)
        (coarsenedLengthsFor_pos D R)
  flat_boundary_cocycle :
    ∀ {R S : RetainedBoundaryPattern D},
      S.Le R →
        boundaryDecorationBundleTotalExcess
            P hPrimitive hReduced u D
            (boundaryDecorationFlatSection D R) =
          deletionCost P hPrimitive hReduced u D R S +
            boundaryDecorationBundleTotalExcess
              P hPrimitive hReduced u D
              (boundaryDecorationFlatSection D S)
  source_total_exact :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D) =
      arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
  source_affine_exact :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (sourceBoundaryDecorationBundlePoint
            P hPrimitive hReduced u D)
  flat_bottom_zero :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D (retainNoBoundaries D)) = 0

/--
## Boundary Decoration Bundle closure theorem

canonical Boolean boundary family は、各 base pattern が決める coarsened record skeleton 上に
local-area product fiber を持つ dependent bundle として組織化できる。各 abstract fiber は
actual same-skeleton source fiber と exact に同値で、内部には product deletion system がある。
flat section の base deletion は既存 arithmetic cocycle に従い、元 source の top-fiber point の
total excess は既存二段階 arithmetic excess と exact に一致する。
-/
theorem boundaryDecorationBundle_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundleClosed
      P hPrimitive hReduced u D := by
  refine {
    bundle_bijective :=
      (boundaryDecorationBundleEquiv
        P hPrimitive hReduced u D).bijective
    coarse_lengths_positive := ?_
    fiber_product_system := ?_
    flat_boundary_cocycle := ?_
    source_total_exact :=
      sourceBoundaryDecorationBundlePoint_totalExcess
        P hPrimitive hReduced u D
    source_affine_exact :=
      affineConst_eq_absoluteBase_add_sourceBoundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
    flat_bottom_zero :=
      boundaryDecorationBundleTotalExcess_flatBottom_eq_zero
        P hPrimitive hReduced u D
  }
  · intro R r hr
    exact coarsenedLengthsFor_pos D R r hr
  · intro R
    exact boundaryDecorationFiber_productDeletionSystem_closed D R
  · intro R S hSR
    exact boundaryDecorationBundleTotalExcess_flatSection_step
      P hPrimitive hReduced u D hSR

end RecordFerrers
end Collatz2
