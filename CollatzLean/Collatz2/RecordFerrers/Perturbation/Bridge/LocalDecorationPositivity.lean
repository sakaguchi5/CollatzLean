import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationGap
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential

/-!
# Record–Ferrers Perturbation / Local Decoration Positivity

`LocalDecorationGap` では、actual source と canonical flat top の local translations を

  actual : [B₁, ..., Bₘ]
  flat   : [B₁⁰, ..., Bₘ⁰]

とし、signed defects `δᵢ = Bᵢ - Bᵢ⁰ : ℤ` の weighted sumとして

  decorationGap = 2 * localWeightedDecorationDefect

を exact に得た。ただし前段では、weighted sum 全体の非負性だけを使い、
各 `δᵢ` の非負性はまだ証明していなかった。

本ファイルではその最後の符号問題を局所的に閉じる。

P30 の canonical flat representative は各 record block 内で excess を左端値に固定する。
したがって flat block の local proper-prefix two-depth は `0,1,2,...` の baseline そのもの。
この事実から各 flat block の affine translation は

  Bᵢ⁰ = baseAffineConst rᵢ = 3^rᵢ - 2^rᵢ

と exact に計算できる。

一方、任意の valid word は fixed-fiber weighted-potential formula により
`baseAffineConst` 以上の affine translation を持つ。従って actual record block ごとに

  Bᵢ⁰ ≤ Bᵢ

であり、全 local decoration defects は componentwise nonnegative になる。

これにより上段 residual は「符号付き local defect の weighted sum」から
「各項が非負な local arithmetic / Ferrers excess の weighted sum」へ強化される。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. canonical flat top の exact excess profile -/

/--
全境界保持 canonical flat top の excess profile は元の record length skeleton を
各 block 内で平坦化した `flatExcessForSkeleton 1 D.lengths` そのもの。
-/
theorem canonicalFlatTop_excessAt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {j : ℕ}
    (hjp : j < P.oddCount) :
    (canonicalFlatTop P hPrimitive hReduced u D).excessAt j =
      flatExcessForSkeleton 1 D.lengths j := by
  simpa [canonicalFlatTop, canonicalFlatPoint] using
    (canonicalFlatRepresentative_excessAt
      P hPrimitive hReduced u D (retainAllBoundaries D) hjp)

/-! ## 2. 一つの flat interval の affine translation は baseline -/

/--
ある interval `[start,start+len)` で global excess が左端値に完全に平坦なら、
その local block の proper-prefix two-depth は exact に `k` となる。
従って local `affineConst` は `baseAffineConst len` に一致する。

terminal exponent は `affineConst` の proper-prefix path terms には現れないので、
この結論には local terminal depth の追加仮定は不要。
-/
theorem affineConst_blockWord_eq_baseAffineConst_of_flat_interval
    {p H : ℕ}
    (x : FiberPoint p H)
    {start len : ℕ}
    (hEnd : start + len ≤ p)
    (hFlat :
      ∀ k : ℕ,
        k < len →
        x.excessAt (start + k) = x.excessAt start) :
    affineConst (blockWord x start len) = baseAffineConst len := by
  have hOdd : oddSteps (blockWord x start len) = len :=
    oddSteps_blockWord x hEnd
  rw [← affinePathSum_eq_affineConst]
  unfold affinePathSum baseAffineConst
  rw [hOdd]
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : k < len := Finset.mem_range.mp hkMem
  have hStartLe : start ≤ p := by omega
  have hKLe : start + k ≤ p := by omega
  have hStart := x.height_eq_index_add_excess hStartLe
  have hK := x.height_eq_index_add_excess hKLe
  have hEx := hFlat k hk
  rw [hEx] at hK
  have hAdd := height_add_eq_add_blockDepth x start k
  have hLocal : twoSteps (blockWord x start k) = k := by
    omega
  have hTake :
      (blockWord x start len).take k = blockWord x start k := by
    simp [blockWord, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  have hDepth :
      prefixTwoDepth (blockWord x start len) k = k := by
    unfold prefixTwoDepth
    rw [hTake]
    exact hLocal
  unfold affinePathTerm baseAffineTerm
  rw [hOdd, hDepth]

/--
平坦 skeleton profile から切り出される全 local block の `affineConst` 列は、
length ごとの `baseAffineConst` 列に exact に一致する。

RecordChain の proof object には依存せず、positive length list、terminal coverage、
flat excess profile だけを使う純粋な slicing lemma。
-/
theorem blockWordsFromLengths_affineConsts_eq_baseMap_of_flat
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ)
    (lengths : List ℕ)
    (hEnd : start + lengths.sum = p)
    (hPos : ∀ r ∈ lengths, 0 < r)
    (hFlat :
      ∀ j : ℕ,
        start ≤ j →
        j < p →
        x.excessAt j = flatExcessForSkeleton start lengths j) :
    (RecordChain.blockWordsFromLengths x start lengths).map affineConst =
      lengths.map baseAffineConst := by
  induction lengths generalizing start with
  | nil =>
      simp [RecordChain.blockWordsFromLengths]
  | cons len rest ih =>
      have hLenPos : 0 < len := hPos len (by simp)
      simp only [List.sum_cons] at hEnd
      have hHeadEnd : start + len ≤ p := by omega
      have hStartLt : start < p := by omega
      have hStartEx :
          x.excessAt start = criticalExcess start := by
        calc
          x.excessAt start =
              flatExcessForSkeleton start (len :: rest) start :=
            hFlat start le_rfl hStartLt
          _ = criticalExcess start :=
            flatExcessForSkeleton_of_head
              start len rest le_rfl
              (Nat.lt_add_of_pos_right hLenPos)
      have hInterval :
          ∀ k : ℕ,
            k < len →
            x.excessAt (start + k) = x.excessAt start := by
        intro k hk
        have hkp : start + k < p := by omega
        calc
          x.excessAt (start + k) =
              flatExcessForSkeleton start (len :: rest) (start + k) :=
            hFlat (start + k) (by omega) hkp
          _ = criticalExcess start :=
            flatExcessForSkeleton_of_head
              start len rest (by omega) (by omega)
          _ = x.excessAt start := hStartEx.symm
      have hHead :
          affineConst (blockWord x start len) = baseAffineConst len :=
        affineConst_blockWord_eq_baseAffineConst_of_flat_interval
          x hHeadEnd hInterval
      have hTailEnd : (start + len) + rest.sum = p := by omega
      have hTailPos : ∀ r ∈ rest, 0 < r := by
        intro r hr
        exact hPos r (by simp [hr])
      have hFlatTail :
          ∀ j : ℕ,
            start + len ≤ j →
            j < p →
            x.excessAt j =
              flatExcessForSkeleton (start + len) rest j := by
        intro j hsj hjp
        calc
          x.excessAt j =
              flatExcessForSkeleton start (len :: rest) j :=
            hFlat j (by omega) hjp
          _ = flatExcessForSkeleton (start + len) rest j :=
            flatExcessForSkeleton_of_after_head
              start len rest hsj
      have hTail := ih (start + len) hTailEnd hTailPos hFlatTail
      simp [RecordChain.blockWordsFromLengths, hHead, hTail]

/-! ## 3. flat-top local baseline の closed form -/

/--
canonical flat top の任意の genuine cut 1 decomposition が元 skeleton を持つなら、
各 block affine translation は length ごとの baseline に exact に一致する。

したがって classical choice された `canonicalFlatTopDecomposition` に固有の性質ではない。
-/
theorem flatTopDecomposition_blockAffineConsts_eq_baseMap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (E : RecordDecomposition
      (canonicalFlatTop P hPrimitive hReduced u D) 1)
    (hE : E.lengths = D.lengths) :
    E.blocks.map affineConst = D.lengths.map baseAffineConst := by
  have hMap :=
    blockWordsFromLengths_affineConsts_eq_baseMap_of_flat
      (canonicalFlatTop P hPrimitive hReduced u D)
      1 D.lengths
      D.start_add_sum_eq_terminal
      D.lengths_pos
      (by
        intro j _hj1 hjp
        exact canonicalFlatTop_excessAt
          P hPrimitive hReduced u D hjp)
  unfold RecordDecomposition.blocks RecordChain.blocks
  rw [hE]
  exact hMap

/--
## 主定理 1: flat local arithmetic baseline は skeleton だけで決まる

flat-top local translation vector は exact に

  [baseAffineConst r₁, ..., baseAffineConst rₘ]

であり、flat decomposition の choice に依存する hidden arithmetic は残らない。
-/
theorem flatTopLocalArithmeticTranslations_eq_baseMap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    flatTopLocalArithmeticTranslations P hPrimitive hReduced u D =
      D.lengths.map baseAffineConst := by
  let E := canonicalFlatTopDecomposition
    P hPrimitive hReduced u D
  have hELen : E.lengths = D.lengths := by
    dsimp [E]
    exact canonicalFlatTopDecomposition_lengths
      P hPrimitive hReduced u D
  have hBlocks :
      E.blocks.map affineConst = D.lengths.map baseAffineConst :=
    flatTopDecomposition_blockAffineConsts_eq_baseMap
      P hPrimitive hReduced u D E hELen
  unfold flatTopLocalArithmeticTranslations canonicalFlatTopCoordinates
  change E.translationCoordinates.map Prod.snd =
    D.lengths.map baseAffineConst
  rw [E.translationCoordinates_eq_blockCoordinateMap]
  simpa [
    List.map_map,
    Function.comp_def,
    blockTranslationCoordinate
  ] using hBlocks

/--
flat local baseline の explicit closed form。

各 length `r` に対して `B⁰ = 3^r - 2^r`。
-/
theorem flatTopLocalArithmeticTranslations_eq_closedForm
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    flatTopLocalArithmeticTranslations P hPrimitive hReduced u D =
      D.lengths.map (fun r => 3 ^ r - 2 ^ r) := by
  rw [flatTopLocalArithmeticTranslations_eq_baseMap
    P hPrimitive hReduced u D]
  simp [baseAffineConst_eq_threePow_sub_twoPow]

/-! ## 4. actual local translations は baseline 以上 -/

/-- valid word をその own `(oddSteps,twoSteps)` fixed fiber の点として読む。 -/
def localFiberPointOfValid
    (w : Word)
    (hValid : Valid w) :
    FiberPoint (oddSteps w) (twoSteps w) :=
  { word := w
    valid := hValid
    oddSteps_eq := rfl
    twoSteps_eq := rfl }

/--
valid word の affine translation は同じ odd length の baseline 以上。
これは fixed-fiber weighted-potential lower bound の local block 版。
-/
theorem baseAffineConst_le_affineConst_of_valid
    (w : Word)
    (hValid : Valid w) :
    baseAffineConst (oddSteps w) ≤ affineConst w := by
  let x := localFiberPointOfValid w hValid
  have h := affineConst_lower_bound x
  rw [← baseAffineConst_eq_threePow_sub_twoPow] at h
  simpa [x, localFiberPointOfValid] using h

/--
valid word の baseline 超過量は、その local fixed fiber における Ferrers weighted area。
従って local translation excess は本質的に局所 Ferrers 面積である。
-/
theorem affineConst_sub_baseAffineConst_eq_localWeightedArea
    (w : Word)
    (hValid : Valid w) :
    affineConst w - baseAffineConst (oddSteps w) =
      weightedArea (localFiberPointOfValid w hValid).toFerrersShape := by
  have h := affineConst_eq_base_add_weightedArea
    (localFiberPointOfValid w hValid)
  have hExact :
      affineConst w =
        baseAffineConst (oddSteps w) +
          weightedArea (localFiberPointOfValid w hValid).toFerrersShape := by
    simpa [localFiberPointOfValid] using h
  omega

/-- 二つの自然数 list の componentwise order。length mismatch は false。 -/
def LocalTranslationPointwiseLe : List ℕ → List ℕ → Prop
  | [], [] => True
  | a :: as, b :: bs =>
      a ≤ b ∧ LocalTranslationPointwiseLe as bs
  | _, _ => False

/-- valid block 列では length-baseline 列が block affine translation 列以下。 -/
theorem baseMap_pointwiseLe_blockAffineConsts
    (bs : List Word)
    (hValid : ∀ b ∈ bs, Valid b) :
    LocalTranslationPointwiseLe
      (bs.map (fun b => baseAffineConst (oddSteps b)))
      (bs.map affineConst) := by
  induction bs with
  | nil =>
      simp [LocalTranslationPointwiseLe]
  | cons b bs ih =>
      have hb : Valid b := hValid b (by simp)
      have hTail : ∀ c ∈ bs, Valid c := by
        intro c hc
        exact hValid c (by simp [hc])
      change
        baseAffineConst (oddSteps b) ≤ affineConst b ∧
          LocalTranslationPointwiseLe
            (bs.map (fun c => baseAffineConst (oddSteps c)))
            (bs.map affineConst)
      exact ⟨
        baseAffineConst_le_affineConst_of_valid b hb,
        ih hTail
      ⟩

/-- source decomposition の local B-vector は skeleton baseline 以上。 -/
theorem baseLocalTranslations_pointwiseLe_actual
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    LocalTranslationPointwiseLe
      (D.lengths.map baseAffineConst)
      (localArithmeticTranslations D) := by
  have h := baseMap_pointwiseLe_blockAffineConsts
    D.blocks D.blocks_valid_public
  rw [← D.blocks_oddSteps_eq_lengths]
  rw [localArithmeticTranslations_eq_blockAffineConsts D]
  simpa [List.map_map, Function.comp_def] using h

/--
## 主定理 2: flat baseline ≤ actual local translations componentwise

各 record block ごとに `Bᵢ⁰ ≤ Bᵢ`。
-/
theorem flatTopLocalArithmeticTranslations_pointwiseLe_actual
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    LocalTranslationPointwiseLe
      (flatTopLocalArithmeticTranslations P hPrimitive hReduced u D)
      (localArithmeticTranslations D) := by
  rw [flatTopLocalArithmeticTranslations_eq_baseMap
    P hPrimitive hReduced u D]
  exact baseLocalTranslations_pointwiseLe_actual D

/-! ## 5. signed local defects は実は componentwise nonnegative -/

/--
componentwise `baseline ≤ actual` なら、`actual - baseline : ℤ` の全成分は非負。
-/
theorem signedLocalTranslationDifference_mem_nonneg
    {actual baseline : List ℕ}
    (hLe : LocalTranslationPointwiseLe baseline actual) :
    ∀ z ∈ signedLocalTranslationDifference actual baseline, 0 ≤ z := by
  induction baseline generalizing actual with
  | nil =>
      cases actual with
      | nil =>
          intro z hz
          simp [signedLocalTranslationDifference] at hz
      | cons a as =>
          simp [LocalTranslationPointwiseLe] at hLe
  | cons b bs ih =>
      cases actual with
      | nil =>
          simp [LocalTranslationPointwiseLe] at hLe
      | cons a as =>
          have hHead : b ≤ a := hLe.1
          have hTail : LocalTranslationPointwiseLe bs as := hLe.2
          intro z hz
          simp only [signedLocalTranslationDifference, List.mem_cons] at hz
          rcases hz with hz | hz
          · subst z
            exact sub_nonneg.mpr (by exact_mod_cast hHead)
          · exact ih hTail z hz

/--
## 主定理 3: local decoration defects は一つずつ非負

前段の global weighted nonnegativity より強く、各 `δᵢ = Bᵢ - Bᵢ⁰` 自体が非負。
-/
theorem localDecorationDefects_componentwise_nonneg
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ∀ z ∈ localDecorationDefects P hPrimitive hReduced u D,
      0 ≤ z := by
  unfold localDecorationDefects
  exact signedLocalTranslationDifference_mem_nonneg
    (flatTopLocalArithmeticTranslations_pointwiseLe_actual
      P hPrimitive hReduced u D)

/-! ## 6. zero decoration の exact characterization -/

/--
`decorationGap = 0` iff actual source 自体が canonical flat top。

したがって上段 arithmetic residual が消えることは、global cancellation ではなく
actual decoration が完全に flat であることを意味する。
-/
theorem decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    decorationGap P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D := by
  constructor
  · intro hGap
    have hAffine := affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced u D
    rw [hGap, Nat.add_zero] at hAffine
    exact fiberPoint_eq_of_same_affineConst hAffine
  · intro hEq
    unfold decorationGap
    have hWord :
        u.word =
          (canonicalFlatTop P hPrimitive hReduced u D).word :=
      congrArg
        (fun x : FiberPoint P.oddCount P.twoDepth => x.word) hEq
    rw [hWord]
    simp

/--
local weighted decoration defect が 0 iff actual source が canonical flat top。
-/
theorem localWeightedDecorationDefect_eq_zero_iff_source_eq_canonicalFlatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    localWeightedDecorationDefect P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D := by
  constructor
  · intro hLocal
    have hGapZ :=
      decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
        P hPrimitive hReduced u D
    rw [hLocal] at hGapZ
    norm_num at hGapZ
    have hGap : decorationGap P hPrimitive hReduced u D = 0 := by
      exact_mod_cast hGapZ
    exact
      (decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
        P hPrimitive hReduced u D).1 hGap
  · intro hFlat
    have hGap : decorationGap P hPrimitive hReduced u D = 0 :=
      (decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
        P hPrimitive hReduced u D).2 hFlat
    have hGapZ :=
      decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
        P hPrimitive hReduced u D
    rw [hGap] at hGapZ
    norm_num at hGapZ
    linarith

/-! ## 7. closure package -/

/-- Local Decoration Positivity 層で閉じた exact facts。 -/
structure LocalDecorationPositivityClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  flat_baseline_exact :
    flatTopLocalArithmeticTranslations P hPrimitive hReduced u D =
      D.lengths.map baseAffineConst
  flat_baseline_closed_form :
    flatTopLocalArithmeticTranslations P hPrimitive hReduced u D =
      D.lengths.map (fun r => 3 ^ r - 2 ^ r)
  baseline_pointwise_le_actual :
    LocalTranslationPointwiseLe
      (flatTopLocalArithmeticTranslations P hPrimitive hReduced u D)
      (localArithmeticTranslations D)
  local_defects_nonnegative :
    ∀ z ∈ localDecorationDefects P hPrimitive hReduced u D,
      0 ≤ z
  zero_gap_iff_flat :
    decorationGap P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D
  zero_weighted_defect_iff_flat :
    localWeightedDecorationDefect P hPrimitive hReduced u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D

/--
## Local Decoration Positivity closure theorem

canonical flat baseline は各 local fixed fiber の absolute baseline
`3^r - 2^r` そのものであり、actual local translation は各 block ごとにそれ以上。
従って `LocalDecorationGap` の signed defects は実は全成分が非負である。
-/
theorem localDecorationPositivity_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    LocalDecorationPositivityClosed P hPrimitive hReduced u D := by
  refine {
    flat_baseline_exact := ?_
    flat_baseline_closed_form := ?_
    baseline_pointwise_le_actual := ?_
    local_defects_nonnegative := ?_
    zero_gap_iff_flat := ?_
    zero_weighted_defect_iff_flat := ?_
  }
  · exact flatTopLocalArithmeticTranslations_eq_baseMap
      P hPrimitive hReduced u D
  · exact flatTopLocalArithmeticTranslations_eq_closedForm
      P hPrimitive hReduced u D
  · exact flatTopLocalArithmeticTranslations_pointwiseLe_actual
      P hPrimitive hReduced u D
  · exact localDecorationDefects_componentwise_nonneg
      P hPrimitive hReduced u D
  · exact decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
      P hPrimitive hReduced u D
  · exact localWeightedDecorationDefect_eq_zero_iff_source_eq_canonicalFlatTop
      P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
