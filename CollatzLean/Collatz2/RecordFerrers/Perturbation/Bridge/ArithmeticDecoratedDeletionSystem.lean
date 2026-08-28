import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationAreaDecomposition
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DeletionPotentialCocycle

/-!
# Record–Ferrers Perturbation / Arithmetic Decorated Deletion System

ここまでで二種類の normalization が独立に閉じた。

上段:

  actual source
      |
      | 2 * positive local Ferrers area potential
      v
  canonical flat top

下段:

  canonical flat top
      |
      | positive path-independent Boolean boundary deletion cocycle
      v
  absolute bottom

本ファイルではこの二段を一個の arithmetic decorated deformation system として束ねる。

中心 formula は自然数上の

  affineConst(actual)
    = absoluteBase
      + boundaryGap
      + 2 * localWeightedDecorationArea

である。

さらに任意の top→bottom actual deletion trace の cost `c` を使っても

  affineConst(actual)
    = absoluteBase + c + 2 * localWeightedDecorationArea

となり、`c = boundaryGap` は deletion path に依存しない。

従って fixed fiber の actual source は

  block 内部の positive local-area normalization
  + block 間の positive confluent boundary deletion

という二種類の独立した下降量を持ち、最終 normal form は ambient fixed fiber の
absolute bottom である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 二段階 normalization の幾何 -/

/--
absolute bottom ≤ canonical flat top ≤ actual source。
上段と下段が同じ Ferrers inclusion の向きに並ぶことを明示する。
-/
theorem arithmeticDecorated_twoStage_ferrers_chain
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint.FerrersLe
        (canonicalFlatBottom P hPrimitive hReduced u D)
        (canonicalFlatTop P hPrimitive hReduced u D) ∧
      FiberPoint.FerrersLe
        (canonicalFlatTop P hPrimitive hReduced u D) u := by
  constructor
  · simpa [canonicalFlatBottom] using
      canonicalNoBoundaryPoint_global_ferrersLe
        P hPrimitive hReduced u D
        (canonicalFlatTop P hPrimitive hReduced u D)
  · exact canonicalFlatTop_ferrersLe_source
      P hPrimitive hReduced u D

/--
二段階 normalization における二つの arithmetic loss を、
それぞれ endpoint の affine constant の exact difference として同時に表示する。

第一段階では actual source から canonical flat top への loss が
`2 * localWeightedDecorationArea` に一致し、
第二段階では canonical flat top から canonical flat bottom への loss が
`boundaryGap` に一致する。

したがって内部 decoration の平坦化と boundary deletion が、
互いに独立な二つの非負 arithmetic contribution として分離される。
-/
theorem arithmeticDecorated_twoStage_affine_exact
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
        affineConst (canonicalFlatTop P hPrimitive hReduced u D).word +
          2 * localWeightedDecorationArea P u D ∧
      affineConst (canonicalFlatTop P hPrimitive hReduced u D).word =
        affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word +
          boundaryGap P hPrimitive hReduced u D := by
  constructor
  · have h := affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced u D
    rw [decorationGap_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D] at h
    exact h
  · exact flatTop_affineConst_eq_bottom_add_boundaryGap
      P hPrimitive hReduced u D

/-! ## 2. total positive excess potential -/

/--
ambient fixed-fiber absolute bottom から actual source までの
total arithmetic excess potential。

canonical flat top から flat bottom までの boundary deletion cost と、
actual source から flat top までの内部 decoration cost
`2 * localWeightedDecorationArea` の和として定義する。

したがって二段階 normalization 全体で失われる arithmetic excess を
一つの自然数値にまとめた量である。
-/
def arithmeticDecoratedTotalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  boundaryGap P hPrimitive hReduced u D +
    2 * localWeightedDecorationArea P u D

/--
actual source の affine constant は、
ambient fixed fiber の absolute base に
total arithmetic excess potential を加えたものに exact に一致する。

すなわち source の arithmetic translation は、
absolute bottom の基準値と二段階 normalization 全体の非負 excess に
完全に分解される。
-/
theorem affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        arithmeticDecoratedTotalExcess P hPrimitive hReduced u D := by
  simpa [arithmeticDecoratedTotalExcess, Nat.add_assoc] using
    affineConst_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D

/--
total arithmetic excess が 0 であることと、
actual source 自身が ambient fixed-fiber canonical flat bottom に一致することは同値。

これは内部 local decoration area と boundary deletion cost の双方が完全に消え、
二段階 normalization の開始点がすでに absolute normal form であることを表す。
-/
theorem arithmeticDecoratedTotalExcess_eq_zero_iff_source_eq_canonicalFlatBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    arithmeticDecoratedTotalExcess P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatBottom P hPrimitive hReduced u D := by
  have hBottom :=
    canonicalNoBoundaryPoint_global_potential_minimum
      P hPrimitive hReduced u D
  have hBottomAffine :
      affineConst (canonicalFlatBottom P hPrimitive hReduced u D).word =
        3 ^ P.oddCount - 2 ^ P.oddCount := by
    simpa [canonicalFlatBottom] using hBottom.2.1
  constructor
  · intro hZero
    have hAffine :=
      affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
    rw [hZero, Nat.add_zero] at hAffine
    apply fiberPoint_eq_of_same_affineConst
    exact hAffine.trans hBottomAffine.symm
  · intro hEq
    have hWord :
        u.word = (canonicalFlatBottom P hPrimitive hReduced u D).word :=
      congrArg
        (fun x : FiberPoint P.oddCount P.twoDepth => x.word) hEq
    have hU :
        affineConst u.word =
          3 ^ P.oddCount - 2 ^ P.oddCount := by
      rw [hWord]
      exact hBottomAffine
    have hAffine :=
      affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
    rw [hU] at hAffine
    omega

/--
total arithmetic excess が strict positive であることと、
actual source が canonical flat bottom と異なることは同値。

従って canonical flat bottom は total excess potential の唯一の零点であり、
それ以外の source では二段階 normalization 全体の arithmetic excess が必ず正になる。
-/
theorem arithmeticDecoratedTotalExcess_pos_iff_source_ne_canonicalFlatBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    0 < arithmeticDecoratedTotalExcess P hPrimitive hReduced u D ↔
      u ≠ canonicalFlatBottom P hPrimitive hReduced u D := by
  constructor
  · intro hPos hEq
    have hZero :=
      (arithmeticDecoratedTotalExcess_eq_zero_iff_source_eq_canonicalFlatBottom
        P hPrimitive hReduced u D).2 hEq
    omega
  · intro hNe
    have hNonzero :
        arithmeticDecoratedTotalExcess P hPrimitive hReduced u D ≠ 0 := by
      intro hZero
      exact hNe
        ((arithmeticDecoratedTotalExcess_eq_zero_iff_source_eq_canonicalFlatBottom
          P hPrimitive hReduced u D).1 hZero)
    exact Nat.pos_of_ne_zero hNonzero

/-! ## 3. 任意 deletion trace を使った integrated formula -/

/--
canonical flat top から flat bottom への任意の actual deletion trace を用いても、
actual source の affine constant は

`absolute base + trace cost + 2 * local weighted decoration area`

へ exact に分解される。

したがって boundary 側では trace の選び方を許したまま、
内部 decoration cost と boundary deletion cost を一つの affine formula に統合できる。
-/
theorem affineConst_eq_absoluteBase_add_traceCost_add_two_mul_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D) c) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) + c +
        2 * localWeightedDecorationArea P u D := by
  have h := affineConst_eq_absoluteBase_add_traceCost_add_decorationGap
    P hPrimitive hReduced u D T
  rw [decorationGap_eq_two_mul_localWeightedDecorationArea
    P hPrimitive hReduced u D] at h
  exact h

/--
canonical top-to-bottom deletion trace が存在し、
その trace cost は exact に `boundaryGap` に一致する。

さらに同じ trace に対して、actual source の affine constant は
absolute base、boundary cost、内部 local decoration area の三項へ exact に分解される。

これにより二段階 normalization の canonical 実現と arithmetic formula を同時に得る。
-/
theorem exists_arithmeticDecorated_top_bottom_normalization
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ActualDeletionTraceCost
        P hPrimitive hReduced u D
        (retainAllBoundaries D) (retainNoBoundaries D)
        (boundaryGap P hPrimitive hReduced u D) ∧
      affineConst u.word =
        (3 ^ P.oddCount - 2 ^ P.oddCount) +
          boundaryGap P hPrimitive hReduced u D +
          2 * localWeightedDecorationArea P u D := by
  constructor
  · exact exists_top_bottom_trace_with_boundaryGap
      P hPrimitive hReduced u D
  · exact affineConst_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D

/-! ## 4. 最終 closure package -/

/--
actual arithmetic decoration と canonical Boolean deletion を統合した最終 closure package。

既存の lossless geometry/arithmetic separation、
block 内部の positive local area decomposition、
有限・terminating・confluent な canonical deletion system、
path-independent boundary deletion cocycle を保持し、

さらに

actual source
→ canonical flat top
→ canonical flat bottom

という二段階 normalization の Ferrers order、
total affine decomposition、
absolute-bottom の零点特徴付け、
canonical deletion trace、
任意 trace に対する integrated affine formula

を一つに束ねる。
-/
structure ArithmeticDecoratedDeletionSystemClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where

  lossless_separation :
    ArithmeticDecorationSeparationClosed P hPrimitive hReduced u D

  local_area_decomposition :
    LocalDecorationAreaDecompositionClosed P hPrimitive hReduced u D

  deletion_system :
    CanonicalActualDeletionSystemClosed P hPrimitive hReduced u D

  deletion_cocycle :
    CanonicalDeletionPotentialCocycleClosed P hPrimitive hReduced u D

  two_stage_ferrers_chain :
    FiberPoint.FerrersLe
        (canonicalFlatBottom P hPrimitive hReduced u D)
        (canonicalFlatTop P hPrimitive hReduced u D) ∧
      FiberPoint.FerrersLe
        (canonicalFlatTop P hPrimitive hReduced u D) u

  total_affine_exact :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        arithmeticDecoratedTotalExcess P hPrimitive hReduced u D

  total_zero_iff_absolute_bottom :
    arithmeticDecoratedTotalExcess P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatBottom P hPrimitive hReduced u D

  canonical_trace :
    ActualDeletionTraceCost
      P hPrimitive hReduced u D
      (retainAllBoundaries D) (retainNoBoundaries D)
      (boundaryGap P hPrimitive hReduced u D)

  trace_affine_exact :
    ∀ {c : ℕ},
      ActualDeletionTraceCost
          P hPrimitive hReduced u D
          (retainAllBoundaries D) (retainNoBoundaries D) c →
        affineConst u.word =
          (3 ^ P.oddCount - 2 ^ P.oddCount) + c +
            2 * localWeightedDecorationArea P u D

/--
## Arithmetic Decorated Deletion System closure theorem

actual Record–Ferrers source は lossless な geometry/arithmetic separation を持つ。

第一段階では block 内部の positive local Ferrers area に従って
canonical flat top へ正規化され、
第二段階では canonical Boolean boundary deletion により
ambient fixed-fiber canonical flat bottom へ
finite・terminating・confluent に正規化される。

この二段階 normalization に伴う全 arithmetic excess は exact に

`boundary positive cocycle + 2 * local positive Ferrers-area potential`

へ分解される。

さらに total excess の唯一の零点は canonical flat bottom であり、
任意の top-to-bottom deletion trace に対しても
同じ integrated affine decomposition が成立する。
-/
theorem arithmeticDecoratedDeletionSystem_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ArithmeticDecoratedDeletionSystemClosed P hPrimitive hReduced u D := by
  refine {
    lossless_separation := arithmeticDecorationSeparation_closed
      P hPrimitive hReduced u D
    local_area_decomposition := localDecorationAreaDecomposition_closed
      P hPrimitive hReduced u D
    deletion_system := canonicalActualDeletionSystem_closed
      P hPrimitive hReduced u D
    deletion_cocycle := canonicalDeletionPotentialCocycle_closed
      P hPrimitive hReduced u D
    two_stage_ferrers_chain := arithmeticDecorated_twoStage_ferrers_chain
      P hPrimitive hReduced u D
    total_affine_exact :=
      affineConst_eq_absoluteBase_add_arithmeticDecoratedTotalExcess
        P hPrimitive hReduced u D
    total_zero_iff_absolute_bottom :=
      arithmeticDecoratedTotalExcess_eq_zero_iff_source_eq_canonicalFlatBottom
        P hPrimitive hReduced u D
    canonical_trace := exists_top_bottom_trace_with_boundaryGap
      P hPrimitive hReduced u D
    trace_affine_exact := ?_
  }
  intro c T
  exact affineConst_eq_absoluteBase_add_traceCost_add_two_mul_localWeightedDecorationArea
    P hPrimitive hReduced u D T

end RecordFerrers
end Collatz2
