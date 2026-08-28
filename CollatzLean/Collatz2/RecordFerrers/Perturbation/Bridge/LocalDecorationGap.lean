import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationSeparation

/-!
# Record–Ferrers Perturbation / Local Decoration Gap

`ArithmeticDecorationSeparation` では actual source を

  canonical flat geometry
  + pure local arithmetic translations [B₁, ..., Bₘ]

へ非冗長かつ lossless に分離した。

本ファイルでは、従来一個の scalar だった `decorationGap` を、各 record block の
local translation defect へ exact に分解する。

canonical flat top の同じ record skeleton 上の baseline translations を

  [B₁⁰, ..., Bₘ⁰]

とし、signed local defects を

  δᵢ = Bᵢ - Bᵢ⁰ : ℤ

と置く。componentwise 非負性はまだ仮定しない。

block affine factorization の係数を skeleton だけから読む weighted evaluator
`weightedLocalDecorationDefect` を導入し、

  coordinateWeightedTranslation(actual)
    - coordinateWeightedTranslation(flat)
  = weightedLocalDecorationDefect(lengths, [δᵢ])

を示す。

さらに genuine cut 1 decomposition では anchor が critical roof 上にあり、
`criticalHeight 1 = 1` なので source / flat top の共通 anchor factor は exact に `2`。
したがって最終的に

  decorationGap
    = 2 * weightedLocalDecorationDefect

を `ℤ` 上の exact identity として得る。

これにより上段 arithmetic residual は global black-box scalar ではなく、
record block ごとの local arithmetic defects の weighted sum として読める。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. flat top の pure local arithmetic baseline -/

/-- canonical flat top の pure local arithmetic translation vector `[B₁⁰,...,Bₘ⁰]`。 -/
noncomputable def flatTopLocalArithmeticTranslations
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : List ℕ :=
  (canonicalFlatTopCoordinates
    P hPrimitive hReduced u D).map Prod.snd

/-- source / flat baseline の signed componentwise difference。 -/
def signedLocalTranslationDifference : List ℕ → List ℕ → List ℤ
  | a :: as, b :: bs => ((a : ℤ) - (b : ℤ)) ::
      signedLocalTranslationDifference as bs
  | _, _ => []

/--
source の pure `B` vector と flat baseline `B⁰` vector の signed local defects。

各成分は `Bᵢ - Bᵢ⁰ : ℤ`。この段階では componentwise 非負性を要求しない。
-/
noncomputable def localDecorationDefects
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : List ℤ :=
  signedLocalTranslationDifference
    (localArithmeticTranslations D)
    (flatTopLocalArithmeticTranslations P hPrimitive hReduced u D)

/-! ## 2. skeleton-weighted signed defect evaluator -/

/--
length skeleton `[r₁,...,rₘ]` と signed local defects `[δ₁,...,δₘ]` から
block affine factorization と同じ係数で global defect を組み立てる。

head coefficient は後続 odd length による `3` 冪、tail は head minimal depth による
`2` 冪を受ける。
-/
def weightedLocalDecorationDefect : List ℕ → List ℤ → ℤ
  | [], [] => 0
  | r :: rs, δ :: ds =>
      ((3 ^ rs.sum : ℕ) : ℤ) * δ +
        ((2 ^ minimalDepth r : ℕ) : ℤ) *
          weightedLocalDecorationDefect rs ds
  | _, _ => 0

/--
二つの `(length,B)` coordinate lists が同じ length skeleton を持つなら、
`coordinateWeightedTranslation` の signed difference は、second components の
signed local defects を同じ skeleton weights で足したものと exact に一致する。
-/
theorem coordinateWeightedTranslation_cast_sub_eq_weightedLocalDecorationDefect
    (xs ys : List (ℕ × ℕ))
    (hLengths : xs.map Prod.fst = ys.map Prod.fst) :
    (coordinateWeightedTranslation xs : ℤ) -
        (coordinateWeightedTranslation ys : ℤ) =
      weightedLocalDecorationDefect
        (xs.map Prod.fst)
        (signedLocalTranslationDifference
          (xs.map Prod.snd) (ys.map Prod.snd)) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp [coordinateWeightedTranslation,
            weightedLocalDecorationDefect,
            signedLocalTranslationDifference]
      | cons y ys =>
          simp at hLengths
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hLengths
      | cons y ys =>
          rcases x with ⟨r, B⟩
          rcases y with ⟨s, C⟩
          simp only [List.map_cons, List.cons.injEq] at hLengths
          have hrs : r = s := hLengths.1
          have hTail : xs.map Prod.fst = ys.map Prod.fst := hLengths.2
          subst s
          have hIH := ih ys hTail
          simp only [
            coordinateWeightedTranslation,
            weightedLocalDecorationDefect,
            signedLocalTranslationDifference,
            List.map_cons,
            coordinateOddSteps
          ]
          rw [← hTail]
          push_cast
          calc
            3 ^ (List.map Prod.fst xs).sum * (B : ℤ) +
                  2 ^ minimalDepth r *
                    (coordinateWeightedTranslation xs : ℤ) -
                (3 ^ (List.map Prod.fst xs).sum * (C : ℤ) +
                  2 ^ minimalDepth r *
                    (coordinateWeightedTranslation ys : ℤ))
                =
              3 ^ (List.map Prod.fst xs).sum * ((B : ℤ) - (C : ℤ)) +
                2 ^ minimalDepth r *
                  ((coordinateWeightedTranslation xs : ℤ) -
                    (coordinateWeightedTranslation ys : ℤ)) := by
                  ring
            _ =
              3 ^ (List.map Prod.fst xs).sum * ((B : ℤ) - (C : ℤ)) +
                2 ^ minimalDepth r *
                  weightedLocalDecorationDefect
                    (xs.map Prod.fst)
                    (signedLocalTranslationDifference
                      (xs.map Prod.snd) (ys.map Prod.snd)) := by
                  rw [hIH]

/-- source に付随する canonical global local-decoration defect。 -/
noncomputable def localWeightedDecorationDefect
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℤ :=
  weightedLocalDecorationDefect
    D.lengths
    (localDecorationDefects P hPrimitive hReduced u D)

/--
source / canonical flat top の coordinate weighted translations の差は
`localWeightedDecorationDefect` そのもの。
-/
theorem coordinateWeightedTranslation_cast_sub_eq_localWeightedDecorationDefect
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (coordinateWeightedTranslation
        (arithmeticDecorationCoordinates D) : ℤ) -
      (coordinateWeightedTranslation
        (canonicalFlatTopCoordinates
          P hPrimitive hReduced u D) : ℤ) =
      localWeightedDecorationDefect
        P hPrimitive hReduced u D := by
  have h :=
    coordinateWeightedTranslation_cast_sub_eq_weightedLocalDecorationDefect
      (arithmeticDecorationCoordinates D)
      (canonicalFlatTopCoordinates P hPrimitive hReduced u D)
      (arithmeticDecorationCoordinates_lengths_eq_flatTop
        P hPrimitive hReduced u D)
  rw [arithmeticDecorationCoordinates_lengths D] at h
  simpa [
    localWeightedDecorationDefect,
    localDecorationDefects,
    localArithmeticTranslations,
    flatTopLocalArithmeticTranslations
  ] using h

/-! ## 3. cut 1 anchor は source / flat top で共通 -/

/-- genuine record decomposition の start は必ず critical roof 上。 -/
theorem RecordDecomposition.startHeight_eq_criticalHeight
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    x.height start = criticalHeight start := by
  rcases D with ⟨lengths, chain⟩
  cases chain with
  | last B hTerminal =>
      exact B.start_roof
  | cons B hInterior T =>
      exact B.start_roof

/-- cut 1 decomposition の anchor prefix two-depth は `criticalHeight 1`。 -/
theorem RecordDecomposition.cutOne_prefixTwoSteps_eq_criticalHeight
    {p H : ℕ}
    {x : FiberPoint p H}
    (D : RecordDecomposition x 1) :
    twoSteps (x.word.take 1) = criticalHeight 1 := by
  have h := D.startHeight_eq_criticalHeight
  simpa [FiberPoint.height, prefixTwoDepth] using h

/-- `criticalHeight 1 = 1`。log の実装展開ではなく critical-height characterisation から示す。 -/
theorem criticalHeight_one : criticalHeight 1 = 1 := by
  have hLower : 1 ≤ criticalHeight 1 :=
    index_le_criticalHeight 1
  have hPow : 2 ^ criticalHeight 1 < 3 ^ (1 : ℕ) :=
    criticalHeight_pow_lt_threePow (by omega)
  have hUpper : criticalHeight 1 < 2 := by
    by_contra hNot
    have hTwo : 2 ≤ criticalHeight 1 := by omega
    have hPowLe :
        2 ^ (2 : ℕ) ≤ 2 ^ criticalHeight 1 :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hTwo
    norm_num at hPow hPowLe
  omega

/-- cut 1 decomposition の anchor prefix two-depth は exact に `1`。 -/
theorem RecordDecomposition.cutOne_prefixTwoSteps_eq_one
    {p H : ℕ}
    {x : FiberPoint p H}
    (D : RecordDecomposition x 1) :
    twoSteps (x.word.take 1) = 1 := by
  rw [D.cutOne_prefixTwoSteps_eq_criticalHeight, criticalHeight_one]

/--
同じ fixed fiber 上で cut 1 genuine decompositions を持つ二点は、
先頭一文字の prefix word が一致する。

両者の first exponent が critical roof depth
`criticalHeight 1` に固定されるため。
-/
theorem cutOnePrefix_eq_of_recordDecompositions
    {p H : ℕ}
    (x y : FiberPoint p H)
    (D : RecordDecomposition x 1)
    (E : RecordDecomposition y 1) :
    x.word.take 1 = y.word.take 1 := by
  have hxRoof := D.startHeight_eq_criticalHeight
  have hyRoof := E.startHeight_eq_criticalHeight
  cases hx : x.word with
  | nil =>
      have hStart := D.start_le_terminal
      have hOdd := x.oddSteps_eq
      rw [hx] at hOdd
      simp [oddSteps] at hOdd
      omega
  | cons a xs =>
      cases hy : y.word with
      | nil =>
          have hStart := E.start_le_terminal
          have hOdd := y.oddSteps_eq
          rw [hy] at hOdd
          simp [oddSteps] at hOdd
          omega
      | cons b ys =>
          have ha : a = criticalHeight 1 := by
            simpa [
              FiberPoint.height,
              prefixTwoDepth,
              twoSteps,
              hx
            ] using hxRoof
          have hb : b = criticalHeight 1 := by
            simpa [
              FiberPoint.height,
              prefixTwoDepth,
              twoSteps,
              hy
            ] using hyRoof
          have hab : a = b := ha.trans hb.symm
          simp only [hab, List.take_succ_cons, List.take_zero]

/-! ## 4. source / flat evaluator difference = 2 × local weighted defect -/

/--
source evaluator と flat-top evaluator の signed difference は、cut 1 anchor factor `2` を除けば
suffix coordinate weighted translation の signed differenceそのもの。
-/
theorem sourceAffineDifference_eq_two_mul_coordinateWeightedDifference
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (sourceAffineFromCoordinates u D : ℤ) -
        (flatTopAffineFromCoordinates
          P hPrimitive hReduced u D : ℤ) =
      2 *
        ((coordinateWeightedTranslation
            (arithmeticDecorationCoordinates D) : ℤ) -
          (coordinateWeightedTranslation
            (canonicalFlatTopCoordinates
              P hPrimitive hReduced u D) : ℤ)) := by
  let F := canonicalFlatTopDecomposition
    P hPrimitive hReduced u D
  let flat := canonicalFlatTop P hPrimitive hReduced u D
  have hPrefix : u.word.take 1 = flat.word.take 1 := by
    exact cutOnePrefix_eq_of_recordDecompositions u flat D F
  have hDepth : twoSteps (u.word.take 1) = 1 :=
    D.cutOne_prefixTwoSteps_eq_one
  have hLengths :=
    arithmeticDecorationCoordinates_lengths_eq_flatTop
      P hPrimitive hReduced u D
  have hOdd :
      coordinateOddSteps (arithmeticDecorationCoordinates D) =
        coordinateOddSteps
          (canonicalFlatTopCoordinates P hPrimitive hReduced u D) := by
    unfold coordinateOddSteps
    rw [hLengths]
  unfold flatTopAffineFromCoordinates
  unfold sourceAffineFromCoordinates
  change
    ((3 ^ coordinateOddSteps (arithmeticDecorationCoordinates D) *
          affineConst (u.word.take 1) +
        2 ^ twoSteps (u.word.take 1) *
          coordinateWeightedTranslation
            (arithmeticDecorationCoordinates D) : ℕ) : ℤ) -
      ((3 ^ coordinateOddSteps
            (canonicalFlatTopCoordinates P hPrimitive hReduced u D) *
          affineConst (flat.word.take 1) +
        2 ^ twoSteps (flat.word.take 1) *
          coordinateWeightedTranslation
            (canonicalFlatTopCoordinates P hPrimitive hReduced u D) : ℕ) : ℤ) =
      2 *
        ((coordinateWeightedTranslation
            (arithmeticDecorationCoordinates D) : ℤ) -
          (coordinateWeightedTranslation
            (canonicalFlatTopCoordinates P hPrimitive hReduced u D) : ℤ))
  rw [← hPrefix, ← hOdd]
  have hFlatDepth : twoSteps (flat.word.take 1) = 1 := by
    rw [← hPrefix]
    exact hDepth
  rw [hDepth]
  push_cast
  norm_num
  ring

/--
source / flat evaluator difference は exact に `2 * localWeightedDecorationDefect`。
-/
theorem sourceAffineDifference_eq_two_mul_localWeightedDecorationDefect
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (sourceAffineFromCoordinates u D : ℤ) -
        (flatTopAffineFromCoordinates
          P hPrimitive hReduced u D : ℤ) =
      2 * localWeightedDecorationDefect
        P hPrimitive hReduced u D := by
  rw [sourceAffineDifference_eq_two_mul_coordinateWeightedDifference
    P hPrimitive hReduced u D]
  rw [coordinateWeightedTranslation_cast_sub_eq_localWeightedDecorationDefect
    P hPrimitive hReduced u D]

/-! ## 5. 主定理: decorationGap の exact local weighted-sum formula -/

/--
## 主定理 1: `decorationGap = 2 * local weighted defect` (`ℤ` cast 版)

従来 global scalar だった `decorationGap` は、同じ canonical record skeleton 上の
actual / flat local translations の signed defects を block-affine weights で足したものの
exact 2 倍である。
-/
theorem decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (decorationGap P hPrimitive hReduced u D : ℤ) =
      2 * localWeightedDecorationDefect
        P hPrimitive hReduced u D := by
  have hGap :=
    affineConst_eq_flatTop_add_decorationGap
      P hPrimitive hReduced u D
  have hGapZ :
      (decorationGap P hPrimitive hReduced u D : ℤ) =
        (affineConst u.word : ℤ) -
          (affineConst
            (canonicalFlatTop P hPrimitive hReduced u D).word : ℤ) := by
    have hCast := congrArg (fun n : ℕ => (n : ℤ)) hGap
    push_cast at hCast
    linarith
  have hEval :=
    sourceAffineDifference_eq_two_mul_localWeightedDecorationDefect
      P hPrimitive hReduced u D
  have hEval' :
      (affineConst u.word : ℤ) -
          (affineConst
            (canonicalFlatTop P hPrimitive hReduced u D).word : ℤ) =
        2 * localWeightedDecorationDefect
          P hPrimitive hReduced u D := by
    simpa using hEval
  exact hGapZ.trans hEval'

/-- global weighted local defect は自動的に nonnegative。componentwise 非負性は不要。 -/
theorem localWeightedDecorationDefect_nonneg
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    0 ≤ localWeightedDecorationDefect
      P hPrimitive hReduced u D := by
  have h := decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    P hPrimitive hReduced u D
  have hGap :
      0 ≤ (decorationGap P hPrimitive hReduced u D : ℤ) := by
    exact Int.natCast_nonneg _
  linarith

/-- local weighted decoration defect は decomposition witness に依存しない。 -/
theorem localWeightedDecorationDefect_independent_of_decomposition
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D E : RecordDecomposition u 1) :
    localWeightedDecorationDefect P hPrimitive hReduced u D =
      localWeightedDecorationDefect P hPrimitive hReduced u E := by
  have hD := decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    P hPrimitive hReduced u D
  have hE := decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    P hPrimitive hReduced u E
  have hGap := decorationGap_independent_of_decomposition
    P hPrimitive hReduced u D E
  rw [hGap] at hD
  linarith

/--
## 主定理 2: three-layer affine decomposition の完全局所化版

actual affine translation は

  absolute base
  + Boolean boundary gap
  + 2 * local weighted decoration defects

へ exact に分解される。
-/
theorem affineConst_cast_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationDefect
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (affineConst u.word : ℤ) =
      ((3 ^ P.oddCount - 2 ^ P.oddCount : ℕ) : ℤ) +
        (boundaryGap P hPrimitive hReduced u D : ℤ) +
        2 * localWeightedDecorationDefect
          P hPrimitive hReduced u D := by
  have hThree :=
    affineConst_eq_absoluteBase_add_boundaryGap_add_decorationGap
      P hPrimitive hReduced u D
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hThree
  push_cast at hCast
  rw [decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    P hPrimitive hReduced u D] at hCast
  exact hCast

/-! ## 6. closure package -/

/-- Local Decoration Gap 層で閉じた exact facts。 -/
structure LocalDecorationGapClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  cut_one_depth_exact :
    twoSteps (u.word.take 1) = 1
  coordinate_difference_exact :
    (coordinateWeightedTranslation
        (arithmeticDecorationCoordinates D) : ℤ) -
      (coordinateWeightedTranslation
        (canonicalFlatTopCoordinates
          P hPrimitive hReduced u D) : ℤ) =
      localWeightedDecorationDefect
        P hPrimitive hReduced u D
  decoration_gap_local_exact :
    (decorationGap P hPrimitive hReduced u D : ℤ) =
      2 * localWeightedDecorationDefect
        P hPrimitive hReduced u D
  global_defect_nonnegative :
    0 ≤ localWeightedDecorationDefect
      P hPrimitive hReduced u D
  three_layer_local_exact :
    (affineConst u.word : ℤ) =
      ((3 ^ P.oddCount - 2 ^ P.oddCount : ℕ) : ℤ) +
        (boundaryGap P hPrimitive hReduced u D : ℤ) +
        2 * localWeightedDecorationDefect
          P hPrimitive hReduced u D

/--
## Local Decoration Gap closure theorem

上段 `decorationGap` は canonical record skeleton 上の local translation defects の
weighted sumへ exact に局所化される。cut 1 anchor が一段なので global residual は
その weighted sum の exact 2 倍である。
-/
theorem localDecorationGap_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    LocalDecorationGapClosed P hPrimitive hReduced u D := by
  refine {
    cut_one_depth_exact := D.cutOne_prefixTwoSteps_eq_one
    coordinate_difference_exact := ?_
    decoration_gap_local_exact := ?_
    global_defect_nonnegative := ?_
    three_layer_local_exact := ?_
  }
  · exact coordinateWeightedTranslation_cast_sub_eq_localWeightedDecorationDefect
      P hPrimitive hReduced u D
  · exact decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
      P hPrimitive hReduced u D
  · exact localWeightedDecorationDefect_nonneg
      P hPrimitive hReduced u D
  · exact
      affineConst_cast_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationDefect
        P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
