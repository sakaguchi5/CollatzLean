import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationBundle

/-!
# Record–Ferrers Perturbation / Boundary Decoration Arithmetic Exactness

`BoundaryDecorationBundle` では、Boolean retained-boundary pattern を base、
各 coarse skeleton 上の local-area product を fiber とする dependent bundle

  Σ R : RetainedBoundaryPattern D,
    LocalAreaTuple (coarsenedLengthsFor D R)

を構成した。

そこでは元 source を top fiber に埋め込んだ一点について

  affineConst source
    = absoluteBase + bundleTotalExcess

まで証明したが、bundle の任意の点についてはまだ genuine arithmetic との完全な同定を
行っていなかった。

本ファイルでは各 abstract bundle point を fiberwise equivalence の逆写像によって actual
`FiberPoint` へ戻し、その全点について

  affineConst (realization Z)
    = (3^p - 2^p) + boundaryDecorationBundleTotalExcess Z

を証明する。

鍵は pattern `R` の actual fiber に属する任意の source `X` について、その source 自身から
再構成した `canonicalFlatTop` が元 bundle base の `canonicalFlatPoint R` と exact に一致する
ことである。従って source-relative `decorationGap` は fiber local-area product の
`2 * weightedArea` となり、base-relative remaining boundary cost と exact に接続できる。

さらに fixed `(p,H)` fiber では `affineConst` が lossless なので、bundle total excess 自体も
bundle 全体で injective になる。従って

  totalExcess Z = totalExcess W ↔ Z = W

であり、absolute-bottom flat bundle point が total excess の唯一の零点になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 各 actual fiber の flat baseline は bundle base の canonical flat point -/

/--
actual fiber source の chosen decomposition が持つ skeleton は、
base pattern `R` の coarse skeleton と一致する。
-/
theorem boundaryDecorationActualFiber_decomposition_lengths
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    X.decomposition.lengths =
      coarsenedLengthsFor D R := by
  calc
    X.decomposition.lengths =
        (boundaryCanonicalDecomposition
          P hPrimitive hReduced u D R).lengths :=
      X.decomposition_lengths
    _ = coarsenedLengthsFor D R :=
      boundaryCanonicalDecomposition_lengths
        P hPrimitive hReduced u D R

/--
boundary decoration actual fiber の canonical flat top と
base pattern `R` の canonical flat point は、
各 proper column の excess を exact に共有する。
-/
theorem boundaryDecorationActualFiber_canonicalFlatTop_excessAt_eq_baseFlatPoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R)
    (i : Fin P.oddCount) :
    (canonicalFlatTop
      P hPrimitive hReduced X.1 X.decomposition).excessAt i.1 =
      (canonicalFlatPoint
        P hPrimitive hReduced u D R).excessAt i.1 := by
  simp only [canonicalFlatTop, canonicalFlatPoint]
  have hXRaw :=
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced
      X.1 X.decomposition
      (retainAllBoundaries X.decomposition)
      i.isLt
  have hX :
      (canonicalFlatRepresentative
        P hPrimitive hReduced
        X.1 X.decomposition
        (retainAllBoundaries X.decomposition)).excessAt i.1 =
        flatExcessForSkeleton
          1 X.decomposition.lengths i.1 := by
    simpa only [
      coarsenedLengthsFor_retainAllBoundaries
    ] using hXRaw
  have hLengths :
      X.decomposition.lengths =
        coarsenedLengthsFor D R :=
    boundaryDecorationActualFiber_decomposition_lengths
      P hPrimitive hReduced u D R X
  have hSkeleton :
      flatExcessForSkeleton
          1 X.decomposition.lengths i.1 =
        flatExcessForSkeleton
          1 (coarsenedLengthsFor D R) i.1 := by
    exact congrArg
      (fun lengths =>
        flatExcessForSkeleton 1 lengths i.1)
      hLengths
  have hBase :=
    canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced
      u D R
      i.isLt
  exact hX.trans (hSkeleton.trans hBase.symm)

/--
boundary decoration actual fiber の canonical flat top は、
base retained-boundary pattern `R` が定める canonical flat point に一致する。

すなわち fiber 内部の decoration をすべて平坦化すると、
元の actual realization に依存する情報は消え、
base boundary pattern だけで決まる flat representative に戻る。
-/
theorem boundaryDecorationActualFiber_canonicalFlatTop_eq_baseFlatPoint
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    canonicalFlatTop
        P hPrimitive hReduced X.1 X.decomposition =
      canonicalFlatPoint P hPrimitive hReduced u D R := by
  apply FiberPoint.toFerrersShape_injective
  apply FerrersShape.ext
  intro i
  change
    (canonicalFlatTop
      P hPrimitive hReduced X.1 X.decomposition).excessAt i.1 =
      (canonicalFlatPoint
        P hPrimitive hReduced u D R).excessAt i.1
  exact
    boundaryDecorationActualFiber_canonicalFlatTop_excessAt_eq_baseFlatPoint
      P hPrimitive hReduced u D R X i

/-! ## 2. actual fiber の local arithmetic は abstract fiber weighted area と exact -/

/--
actual fiber source の chosen decomposition が持つ local weighted decoration area は、
`boundaryDecorationFiberEquiv` で得る abstract local-area fiber coordinate の
`weightedArea` と exact に一致する。
-/
theorem boundaryDecorationActualFiber_localWeightedDecorationArea_eq_fiberWeightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    localWeightedDecorationArea P X.1 X.decomposition =
      (boundaryDecorationFiberEquiv
        P hPrimitive hReduced u D R X).weightedArea := by
  rw [boundaryDecorationFiberEquiv_weightedArea
    P hPrimitive hReduced u D R X]
  unfold localWeightedDecorationArea
  exact
    (fixedSkeletonLocalAreaTuple_weightedArea_eq_recordLocalWeightedDecorationArea
      P hPrimitive hReduced
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (boundaryCanonicalDecomposition
        P hPrimitive hReduced u D R)
      X).symm

/--
actual fiber source の source-relative `decorationGap` は、abstract fiber weighted area の
exact 2 倍。
-/
theorem boundaryDecorationActualFiber_decorationGap_eq_two_mul_fiberWeightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    decorationGap P hPrimitive hReduced X.1 X.decomposition =
      2 *
        (boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X).weightedArea := by
  rw [decorationGap_eq_two_mul_localWeightedDecorationArea
    P hPrimitive hReduced X.1 X.decomposition]
  rw [
    boundaryDecorationActualFiber_localWeightedDecorationArea_eq_fiberWeightedArea
      P hPrimitive hReduced u D R X
  ]

/-! ## 3. 任意 actual fiber source の affine arithmetic exactness -/

/--
pattern `R` の arbitrary decorated actual source は、base flat affine potential と
fiber local-area potential に exact 分解する。

  affineConst X
    = flatAffine R + 2 * fiberWeightedArea X
-/
theorem boundaryDecorationActualFiber_affineConst_eq_flatAffine_add_two_mul_weightedArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    affineConst X.1.word =
      flatAffine P hPrimitive hReduced u D R +
        2 *
          (boundaryDecorationFiberEquiv
            P hPrimitive hReduced u D R X).weightedArea := by
  have h :=
    affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced X.1 X.decomposition
  rw [
    boundaryDecorationActualFiber_canonicalFlatTop_eq_baseFlatPoint
      P hPrimitive hReduced u D R X,
    boundaryDecorationActualFiber_decorationGap_eq_two_mul_fiberWeightedArea
      P hPrimitive hReduced u D R X
  ] at h
  simpa [flatAffine] using h

/--
## Fiber Arithmetic Exactness

任意 actual fiber source の genuine `affineConst` は

  absolute base
  + remaining boundary residual of R
  + 2 * fiber weighted area

に exact 分解する。
-/
theorem boundaryDecorationActualFiber_affineConst_eq_absoluteBase_add_totalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    affineConst X.1.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        (boundaryResidualToBottom
            P hPrimitive hReduced u D R +
          2 *
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X).weightedArea) := by
  calc
    affineConst X.1.word =
        flatAffine P hPrimitive hReduced u D R +
          2 *
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X).weightedArea :=
      boundaryDecorationActualFiber_affineConst_eq_flatAffine_add_two_mul_weightedArea
        P hPrimitive hReduced u D R X
    _ =
        ((3 ^ P.oddCount - 2 ^ P.oddCount) +
            boundaryResidualToBottom
              P hPrimitive hReduced u D R) +
          2 *
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X).weightedArea := by
      rw [flatAffine_eq_absoluteBase_add_boundaryResidualToBottom
        P hPrimitive hReduced u D R]
    _ =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          (boundaryResidualToBottom
              P hPrimitive hReduced u D R +
            2 *
              (boundaryDecorationFiberEquiv
                P hPrimitive hReduced u D R X).weightedArea) := by
      omega

/-! ## 4. actual bundle 全体の exact formula -/

/--
actual dependent bundle の任意点について、genuine `affineConst` は abstract bundle image の
`boundaryDecorationBundleTotalExcess` と exact に一致する。
-/
theorem boundaryDecorationActualBundle_affineConst_eq_absoluteBase_add_totalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationActualBundle
      P hPrimitive hReduced u D) :
    affineConst Z.2.1.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (boundaryDecorationBundleEquiv
            P hPrimitive hReduced u D Z) := by
  rcases Z with ⟨R, X⟩
  change
    affineConst X.1.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        (boundaryResidualToBottom P hPrimitive hReduced u D R +
          2 *
            (boundaryDecorationFiberEquiv
              P hPrimitive hReduced u D R X).weightedArea)
  exact
    boundaryDecorationActualFiber_affineConst_eq_absoluteBase_add_totalExcess
      P hPrimitive hReduced u D R X

/-! ## 5. abstract bundle point の canonical actual realization -/

/--
abstract boundary-decoration bundle point を fiberwise equivalence の逆写像で actual
fixed-fiber point に戻す。
-/
noncomputable def boundaryDecorationBundleRealization
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    FiberPoint P.oddCount P.twoDepth :=
  ((boundaryDecorationBundleEquiv
      P hPrimitive hReduced u D).symm Z).2.1

/--
## Bundle Arithmetic Exactness 主定理

bundle の任意点 `Z` について、その canonical actual realization の genuine `affineConst` は
absolute base と bundle total excess の和に exact に一致する。
-/
theorem boundaryDecorationBundleRealization_affineConst
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D Z).word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z := by
  let e := boundaryDecorationBundleEquiv
    P hPrimitive hReduced u D
  have h :=
    boundaryDecorationActualBundle_affineConst_eq_absoluteBase_add_totalExcess
      P hPrimitive hReduced u D (e.symm Z)
  rw [e.apply_symm_apply Z] at h
  simpa [boundaryDecorationBundleRealization, e] using h

/-! ## 6. bundle realization は点を取り違えない -/

/--
actual bundle から underlying fixed-fiber point を忘却する写像は injective。

同じ point なら canonical RecordDecomposition の length list も同じであり、
`coarsenedLengthsFor D` の injectivity から base boundary pattern が同じになる。
その後は同じ fixed-skeleton subtype 内の point equality で fiber data も一致する。
-/
theorem boundaryDecorationActualBundle_point_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (fun Z : BoundaryDecorationActualBundle
          P hPrimitive hReduced u D => Z.2.1) := by
  intro A B hPoint
  rcases A with ⟨R, X⟩
  rcases B with ⟨S, Y⟩
  have hChosenLengths :
      X.decomposition.lengths = Y.decomposition.lengths :=
    RecordDecomposition.lengths_unique_of_point_eq
      hPoint X.decomposition Y.decomposition
  have hCoarse :
      coarsenedLengthsFor D R =
        coarsenedLengthsFor D S := by
    calc
      coarsenedLengthsFor D R =
          (boundaryCanonicalDecomposition
            P hPrimitive hReduced u D R).lengths :=
        (boundaryCanonicalDecomposition_lengths
          P hPrimitive hReduced u D R).symm
      _ = X.decomposition.lengths := X.decomposition_lengths.symm
      _ = Y.decomposition.lengths := hChosenLengths
      _ = (boundaryCanonicalDecomposition
            P hPrimitive hReduced u D S).lengths :=
        Y.decomposition_lengths
      _ = coarsenedLengthsFor D S :=
        boundaryCanonicalDecomposition_lengths
          P hPrimitive hReduced u D S
  have hRS : R = S :=
    coarsenedLengthsFor_injective D hCoarse
  subst S
  have hXY : X = Y := by
    apply Subtype.ext
    exact hPoint
  subst Y
  rfl

/-- abstract bundle の canonical realization も injective。 -/
theorem boundaryDecorationBundleRealization_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (boundaryDecorationBundleRealization
        P hPrimitive hReduced u D) := by
  intro Z W hPoint
  let e := boundaryDecorationBundleEquiv
    P hPrimitive hReduced u D
  change (e.symm Z).2.1 = (e.symm W).2.1 at hPoint
  have hActual : e.symm Z = e.symm W :=
    boundaryDecorationActualBundle_point_injective
      P hPrimitive hReduced u D hPoint
  exact e.symm.injective hActual

/-! ## 7. total excess は bundle 全体の lossless scalar coordinate -/

/--
`boundaryDecorationBundleTotalExcess` は bundle 全体で injective。

これは arbitrary bundle point での affine exactness と fixed-fiber `affineConst` の lossless 性を
合成したもの。
-/
theorem boundaryDecorationBundleTotalExcess_injective
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    Function.Injective
      (boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D) := by
  intro Z W hTotal
  apply boundaryDecorationBundleRealization_injective
    P hPrimitive hReduced u D
  apply fiberPoint_eq_of_same_affineConst
  calc
    affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D Z).word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z :=
      boundaryDecorationBundleRealization_affineConst
        P hPrimitive hReduced u D Z
    _ =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D W := by
      rw [hTotal]
    _ =
      affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D W).word :=
      (boundaryDecorationBundleRealization_affineConst
        P hPrimitive hReduced u D W).symm

/-- bundle total excess equality は bundle point equality と exact に同値。 -/
theorem boundaryDecorationBundleTotalExcess_eq_iff_eq
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z W : BoundaryDecorationBundle D) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z =
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D W ↔
      Z = W := by
  constructor
  · exact fun h =>
      boundaryDecorationBundleTotalExcess_injective
        P hPrimitive hReduced u D h
  · intro h
    subst W
    rfl

/-! ## 8. source / flat section / absolute bottom の realization -/

/-- bundle の canonical absolute-bottom point。 -/
def boundaryDecorationBundleBottom
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundle D :=
  boundaryDecorationFlatSection D (retainNoBoundaries D)

/-- canonical bundle bottom の total excess は 0。 -/
@[simp] theorem boundaryDecorationBundleBottom_totalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D
      (boundaryDecorationBundleBottom D) = 0 := by
  simpa [boundaryDecorationBundleBottom] using
    boundaryDecorationBundleTotalExcess_flatBottom_eq_zero
      P hPrimitive hReduced u D

/-- total excess の零点は canonical bundle bottom に限る。 -/
theorem boundaryDecorationBundleTotalExcess_eq_zero_iff_eq_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z = 0 ↔
      Z = boundaryDecorationBundleBottom D := by
  constructor
  · intro hZero
    apply boundaryDecorationBundleTotalExcess_injective
      P hPrimitive hReduced u D
    calc
      boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z = 0 := hZero
      _ = boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (boundaryDecorationBundleBottom D) :=
        (boundaryDecorationBundleBottom_totalExcess
          P hPrimitive hReduced u D).symm
  · intro hEq
    subst Z
    exact boundaryDecorationBundleBottom_totalExcess
      P hPrimitive hReduced u D

/-- flat section `R` の canonical realization は base の `canonicalFlatPoint R` そのもの。 -/
theorem boundaryDecorationBundleRealization_flatSection
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D) :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D R) =
      canonicalFlatPoint P hPrimitive hReduced u D R := by
  apply fiberPoint_eq_of_same_affineConst
  calc
    affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D
          (boundaryDecorationFlatSection D R)).word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (boundaryDecorationFlatSection D R) :=
      boundaryDecorationBundleRealization_affineConst
        P hPrimitive hReduced u D
        (boundaryDecorationFlatSection D R)
    _ =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryResidualToBottom
          P hPrimitive hReduced u D R := by
      rw [boundaryDecorationBundleTotalExcess_flatSection]
    _ = flatAffine P hPrimitive hReduced u D R :=
      (flatAffine_eq_absoluteBase_add_boundaryResidualToBottom
        P hPrimitive hReduced u D R).symm
    _ = affineConst
        (canonicalFlatPoint P hPrimitive hReduced u D R).word := by
      rfl

/-- canonical bundle bottom の realization は P35 の no-boundary absolute point。 -/
theorem boundaryDecorationBundleRealization_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (boundaryDecorationBundleBottom D) =
      canonicalNoBoundaryPoint P hPrimitive hReduced u D := by
  simpa [boundaryDecorationBundleBottom, canonicalNoBoundaryPoint] using
    boundaryDecorationBundleRealization_flatSection
      P hPrimitive hReduced u D (retainNoBoundaries D)

/-- 元 source の top-fiber bundle point を realization すると元 actual source に exact に戻る。 -/
theorem boundaryDecorationBundleRealization_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D) = u := by
  apply fiberPoint_eq_of_same_affineConst
  calc
    affineConst
        (boundaryDecorationBundleRealization
          P hPrimitive hReduced u D
          (sourceBoundaryDecorationBundlePoint
            P hPrimitive hReduced u D)).word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D
          (sourceBoundaryDecorationBundlePoint
            P hPrimitive hReduced u D) :=
      boundaryDecorationBundleRealization_affineConst
        P hPrimitive hReduced u D
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D)
    _ =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        arithmeticDecoratedTotalExcess
          P hPrimitive hReduced u D := by
      rw [sourceBoundaryDecorationBundlePoint_totalExcess]
    _ = affineConst u.word :=
      (affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D).symm

/-! ## 9. closure package -/

/--
Boundary Decoration Arithmetic Exactness 層で閉じた内容。

* bundle 全点の canonical actual realization
* arbitrary fiber point の affine arithmetic exact decomposition
* bundle total excess = realization の genuine affine height above absolute base
* realization injectivity
* total excess の lossless injectivity
* canonical bottom の unique zero
* flat section / source embedding の exact realization
-/
structure BoundaryDecorationArithmeticExactnessClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  realization_injective :
    Function.Injective
      (boundaryDecorationBundleRealization
        P hPrimitive hReduced u D)
  affine_exact :
    ∀ Z : BoundaryDecorationBundle D,
      affineConst
          (boundaryDecorationBundleRealization
            P hPrimitive hReduced u D Z).word =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          boundaryDecorationBundleTotalExcess
            P hPrimitive hReduced u D Z
  total_excess_injective :
    Function.Injective
      (boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D)
  zero_iff_bottom :
    ∀ Z : BoundaryDecorationBundle D,
      boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z = 0 ↔
        Z = boundaryDecorationBundleBottom D
  flat_section_realizes :
    ∀ R : RetainedBoundaryPattern D,
      boundaryDecorationBundleRealization
          P hPrimitive hReduced u D
          (boundaryDecorationFlatSection D R) =
        canonicalFlatPoint P hPrimitive hReduced u D R
  source_realizes :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (sourceBoundaryDecorationBundlePoint
          P hPrimitive hReduced u D) = u

/--
## Boundary Decoration Arithmetic Exactness closure theorem

`BoundaryDecorationBundle` の abstract total excess は、bundle 全点について canonical actual
realization の genuine `affineConst` から absolute base を除いた exact height である。
さらに fixed-fiber affine lossless 性により、この scalar total excess 自体が bundle point を
一意に決め、canonical no-boundary flat point が唯一の zero state になる。
-/
theorem boundaryDecorationArithmeticExactness_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationArithmeticExactnessClosed
      P hPrimitive hReduced u D := by
  exact {
    realization_injective :=
      boundaryDecorationBundleRealization_injective
        P hPrimitive hReduced u D
    affine_exact :=
      boundaryDecorationBundleRealization_affineConst
        P hPrimitive hReduced u D
    total_excess_injective :=
      boundaryDecorationBundleTotalExcess_injective
        P hPrimitive hReduced u D
    zero_iff_bottom :=
      boundaryDecorationBundleTotalExcess_eq_zero_iff_eq_bottom
        P hPrimitive hReduced u D
    flat_section_realizes :=
      boundaryDecorationBundleRealization_flatSection
        P hPrimitive hReduced u D
    source_realizes :=
      boundaryDecorationBundleRealization_source
        P hPrimitive hReduced u D
  }

end RecordFerrers
end Collatz2
