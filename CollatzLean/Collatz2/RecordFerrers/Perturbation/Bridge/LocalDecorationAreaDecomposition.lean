import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationPositivity

/-!
# Record–Ferrers Perturbation / Local Decoration Area Decomposition

`LocalDecorationPositivity` までで、actual block の local translation `Bᵢ` と
canonical flat baseline `Bᵢ⁰` について

  Bᵢ⁰ = baseAffineConst rᵢ = 3^rᵢ - 2^rᵢ
  Bᵢ⁰ ≤ Bᵢ

が各成分ごとに exact に分かった。

本ファイルでは signed defect を完全に捨て、各 actual local block 自身の
Ferrers weighted area を自然数の decoration datum として使う。

一つの valid word `w` に対し

  localDecorationArea w
    = affineConst w - baseAffineConst (oddSteps w)

と置く。既存 weighted-potential formula により、これは exact に
その local fixed fiber の Ferrers weighted area である。

さらに block affine factorization と同じ skeleton weights で local areas を集約する
`weightedLocalDecorationArea` を導入し、最終的に自然数上で

  decorationGap = 2 * localWeightedDecorationArea

を得る。

従って上段 residual は signed arithmetic difference ではなく、
各項が自然数である local Ferrers areas の positive weighted sum になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. 一つの local block の decoration area -/

/--
local word が baseline `1,1,...` より余分に持つ affine translation。
valid word では local Ferrers weighted area と exact に一致する。
-/
def localDecorationArea (w : Word) : ℕ :=
  affineConst w - baseAffineConst (oddSteps w)

/-- local decoration area は local fixed fiber の Ferrers weighted area。 -/
theorem localDecorationArea_eq_weightedArea
    (w : Word)
    (hValid : Valid w) :
    localDecorationArea w =
      weightedArea (localFiberPointOfValid w hValid).toFerrersShape := by
  simpa [localDecorationArea] using
    affineConst_sub_baseAffineConst_eq_localWeightedArea w hValid

/-- valid local word の affine translation は baseline + local area に exact 分解する。 -/
theorem affineConst_eq_baseAffineConst_add_localDecorationArea
    (w : Word)
    (hValid : Valid w) :
    affineConst w =
      baseAffineConst (oddSteps w) + localDecorationArea w := by
  have hLe := baseAffineConst_le_affineConst_of_valid w hValid
  unfold localDecorationArea
  omega

/-- decomposition の actual blocks が持つ自然数 local Ferrers area vector。 -/
def localDecorationAreas
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : List ℕ :=
  D.blocks.map localDecorationArea

/-- local area vector の各成分は当然非負。 -/
theorem localDecorationAreas_nonnegative
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    ∀ A ∈ localDecorationAreas D, 0 ≤ A := by
  intro A hA
  exact Nat.zero_le A

/-- local area vector は record skeleton と同じ長さを持つ。 -/
theorem localDecorationAreas_length
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) :
    (localDecorationAreas D).length = D.lengths.length := by
  unfold localDecorationAreas
  have h := congrArg List.length D.blocks_oddSteps_eq_lengths
  simpa using h

/-! ## 2. actual - baseline の自然数 difference vector -/

/-- componentwise Nat subtraction。length mismatch ではそこで打ち切る。 -/
def natLocalTranslationDifference : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs =>
      (a - b) :: natLocalTranslationDifference as bs
  | _, _ => []

/-- concrete block 列では `affineConst - baseline` 列は local area 列そのもの。 -/
theorem natLocalTranslationDifference_blockAffine_base_eq_areas
    (bs : List Word) :
    natLocalTranslationDifference
        (bs.map affineConst)
        (bs.map (fun b => baseAffineConst (oddSteps b))) =
      bs.map localDecorationArea := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [natLocalTranslationDifference, localDecorationArea, ih]

/--
source local translations から flat baseline を Nat subtraction すると、
exact に actual block の local Ferrers area vectorになる。
-/
theorem natLocalTranslationDifference_actual_flat_eq_localDecorationAreas
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    natLocalTranslationDifference
        (localArithmeticTranslations D)
        (flatTopLocalArithmeticTranslations
          P hPrimitive hReduced u D) =
      localDecorationAreas D := by
  rw [localArithmeticTranslations_eq_blockAffineConsts D]
  rw [flatTopLocalArithmeticTranslations_eq_baseMap
    P hPrimitive hReduced u D]
  rw [← D.blocks_oddSteps_eq_lengths]
  simpa [localDecorationAreas, List.map_map, Function.comp_def] using
    natLocalTranslationDifference_blockAffine_base_eq_areas D.blocks

/-! ## 3. skeleton-weighted Nat evaluator -/

/--
length skeleton と local translation vector から block-affine weights で
一個の global translation contribution を作る補助 evaluator。
-/
def weightedLocalTranslation : List ℕ → List ℕ → ℕ
  | [], [] => 0
  | r :: rs, B :: Bs =>
      3 ^ rs.sum * B +
        2 ^ minimalDepth r * weightedLocalTranslation rs Bs
  | _, _ => 0

/-- coordinate evaluator は first/second projection を分けても同じ。 -/
theorem coordinateWeightedTranslation_eq_weightedLocalTranslation
    (cs : List (ℕ × ℕ)) :
    coordinateWeightedTranslation cs =
      weightedLocalTranslation
        (cs.map Prod.fst) (cs.map Prod.snd) := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      rcases c with ⟨r, B⟩
      simp [coordinateWeightedTranslation, weightedLocalTranslation,
        coordinateOddSteps, ih]

/--
length skeleton と local Ferrers area vector を block affine factorization と同じ重みで集約する。
全演算は Nat 上で行う。
-/
def weightedLocalDecorationArea : List ℕ → List ℕ → ℕ
  | [], [] => 0
  | r :: rs, A :: As =>
      3 ^ rs.sum * A +
        2 ^ minimalDepth r * weightedLocalDecorationArea rs As
  | _, _ => 0

/--
componentwise `baseline ≤ actual` なら、weighted translation の差は
Nat subtraction vector の weighted local area と exact に加法分解する。
-/
theorem weightedLocalTranslation_eq_baseline_add_area
    (lengths actual baseline : List ℕ)
    (hLe : LocalTranslationPointwiseLe baseline actual) :
    weightedLocalTranslation lengths actual =
      weightedLocalTranslation lengths baseline +
        weightedLocalDecorationArea lengths
          (natLocalTranslationDifference actual baseline) := by
  induction lengths generalizing actual baseline with
  | nil =>
      cases actual <;> cases baseline <;>
        simp [weightedLocalTranslation, weightedLocalDecorationArea,
          natLocalTranslationDifference]
  | cons r rs ih =>
      cases actual with
      | nil =>
          cases baseline with
          | nil =>
              simp [weightedLocalTranslation, weightedLocalDecorationArea,
                natLocalTranslationDifference]
          | cons b bs =>
              simp [LocalTranslationPointwiseLe] at hLe
      | cons a as =>
          cases baseline with
          | nil =>
              simp [LocalTranslationPointwiseLe] at hLe
          | cons b bs =>
              have hHead : b ≤ a := hLe.1
              have hTail : LocalTranslationPointwiseLe bs as := hLe.2
              have hIH := ih as bs hTail
              have hHeadEq : a = b + (a - b) := by
                omega
              simp only [weightedLocalTranslation,
                weightedLocalDecorationArea,
                natLocalTranslationDifference]
              rw [hIH, hHeadEq]
              ring_nf
              simp
              omega

/--
genuine record decomposition 自体に付随する natural-number local area potential。

各 block の local decoration area を length skeleton に従って重み付き和した純粋な量であり、
`ContractingExponentPair` や primitive / reduced 仮定には依存しない。
-/
def recordLocalWeightedDecorationArea
    {p H : ℕ}
    {u : FiberPoint p H}
    (D : RecordDecomposition u 1) : ℕ :=
  weightedLocalDecorationArea D.lengths (localDecorationAreas D)

/--
`ContractingExponentPair P` の fixed fiber 上の source decomposition に付随する
canonical natural-number local area potential。

値そのものは `recordLocalWeightedDecorationArea` によって
record decomposition だけから定まり、
ここでは fiber parameters を `P.oddCount`, `P.twoDepth` に特殊化している。
-/
def localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : ℕ :=
  recordLocalWeightedDecorationArea D

/--
actual arithmetic decoration の weighted translation は、
canonical flat top の weighted translation に
source record decomposition 自体が持つ local weighted decoration area を加えたものに exact に一致する。

したがって actual と flat baseline の差は、
各 block の非負 local decoration area を length skeleton の affine weight で
集約した自然数値として表される。
-/
theorem coordinateWeightedTranslation_actual_eq_flat_add_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    coordinateWeightedTranslation (arithmeticDecorationCoordinates D) =
      coordinateWeightedTranslation
          (canonicalFlatTopCoordinates P hPrimitive hReduced u D) +
        localWeightedDecorationArea P u D := by
  rw [coordinateWeightedTranslation_eq_weightedLocalTranslation]
  rw [coordinateWeightedTranslation_eq_weightedLocalTranslation]
  rw [arithmeticDecorationCoordinates_lengths D]
  rw [canonicalFlatTopCoordinates_lengths
    P hPrimitive hReduced u D]
  change
    weightedLocalTranslation D.lengths (localArithmeticTranslations D) =
      weightedLocalTranslation D.lengths
          (flatTopLocalArithmeticTranslations
            P hPrimitive hReduced u D) +
        localWeightedDecorationArea P u D
  have h := weightedLocalTranslation_eq_baseline_add_area
    D.lengths
    (localArithmeticTranslations D)
    (flatTopLocalArithmeticTranslations P hPrimitive hReduced u D)
    (flatTopLocalArithmeticTranslations_pointwiseLe_actual
      P hPrimitive hReduced u D)
  rw [natLocalTranslationDifference_actual_flat_eq_localDecorationAreas
    P hPrimitive hReduced u D] at h
  simpa [localWeightedDecorationArea, recordLocalWeightedDecorationArea] using h

/-! ## 4. signed defect evaluator と Nat area evaluator の一致 -/

/--
signed weighted local defect は、
source record decomposition の natural-number local weighted decoration area を
整数へ cast したものに exact に一致する。

すなわち signed defect 表現に見えていた量には実際には cancellation はなく、
全体が非負な natural-number area によって表現できる。
-/
theorem localWeightedDecorationDefect_eq_cast_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    localWeightedDecorationDefect P hPrimitive hReduced u D =
      (localWeightedDecorationArea P u D : ℤ) := by
  have hDiff :=
    coordinateWeightedTranslation_cast_sub_eq_localWeightedDecorationDefect
      P hPrimitive hReduced u D
  have hNat :=
    coordinateWeightedTranslation_actual_eq_flat_add_localWeightedDecorationArea
      P hPrimitive hReduced u D
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hCast
  have hAreaDiff :
      (coordinateWeightedTranslation
          (arithmeticDecorationCoordinates D) : ℤ) -
        (coordinateWeightedTranslation
          (canonicalFlatTopCoordinates
            P hPrimitive hReduced u D) : ℤ) =
        (localWeightedDecorationArea P u D : ℤ) := by
    linarith
  exact hDiff.symm.trans hAreaDiff

/-! ## 5. 主定理: decorationGap は positive local Ferrers area sum -/

/--
## 主定理 1

canonical `decorationGap` は自然数上で exact に
`2 * localWeightedDecorationArea` に一致する。

したがって actual source から canonical flat top への arithmetic loss は、
各 block の非負 local Ferrers area を skeleton weight で集約した
positive weighted sum のちょうど2倍であり、
signed cancellation は完全に消去される。
-/
theorem decorationGap_eq_two_mul_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    decorationGap P hPrimitive hReduced u D =
      2 * localWeightedDecorationArea P u D := by
  have h := decorationGap_cast_eq_two_mul_localWeightedDecorationDefect
    P hPrimitive hReduced u D
  rw [localWeightedDecorationDefect_eq_cast_localWeightedDecorationArea
    P hPrimitive hReduced u D] at h
  exact_mod_cast h

/--
## 主定理 2

`affineConst u.word` の three-layer decomposition は、
signed defect を用いず、完全に自然数上の positive area decomposition として書ける。

すなわち source の affine constant は

`absolute base + boundary gap + 2 * local weighted decoration area`

に exact に分解される。
-/
theorem affineConst_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryGap P hPrimitive hReduced u D +
        2 * localWeightedDecorationArea P u D := by
  have h := affineConst_eq_absoluteBase_add_boundaryGap_add_decorationGap
    P hPrimitive hReduced u D
  rw [decorationGap_eq_two_mul_localWeightedDecorationArea
    P hPrimitive hReduced u D] at h
  exact h

/--
source record decomposition の local weighted decoration area が 0 であることと、
source point 自身が canonical flat top に一致することは同値。

したがってこの area potential は、
canonical flat top からの deviation を自然数値で完全に検出する。
-/
theorem localWeightedDecorationArea_eq_zero_iff_source_eq_canonicalFlatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    localWeightedDecorationArea P u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D := by
  constructor
  · intro hArea
    apply (decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
      P hPrimitive hReduced u D).1
    rw [decorationGap_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D, hArea]
  · intro hFlat
    have hGap :=
      (decorationGap_eq_zero_iff_source_eq_canonicalFlatTop
        P hPrimitive hReduced u D).2 hFlat
    rw [decorationGap_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D] at hGap
    omega

/--
source record decomposition の local weighted decoration area が strict positive であることと、
source point が canonical flat top と異なることは同値。

従って canonical flat top はこの area potential の唯一の零点であり、
それ以外の genuine source では area は必ず正になる。
-/
theorem localWeightedDecorationArea_pos_iff_source_ne_canonicalFlatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    0 < localWeightedDecorationArea P u D ↔
      u ≠ canonicalFlatTop P hPrimitive hReduced u D := by
  constructor
  · intro hPos hEq
    have hZero :=
      (localWeightedDecorationArea_eq_zero_iff_source_eq_canonicalFlatTop
        P hPrimitive hReduced u D).2 hEq
    omega
  · intro hNe
    have hNonzero :
        localWeightedDecorationArea P u D ≠ 0 := by
      intro hZero
      exact hNe
        ((localWeightedDecorationArea_eq_zero_iff_source_eq_canonicalFlatTop
          P hPrimitive hReduced u D).1 hZero)
    exact Nat.pos_of_ne_zero hNonzero

/-! ## 6. closure package -/

/--
Local Decoration Area Decomposition 層で得られた exact facts をまとめた closure package。

local area vector の長さ整合性、
actual / flat weighted translation の exact area decomposition、
signed defect と natural area の一致、
`decorationGap` の positive area 表現、
three-layer affine decomposition の natural-number area 表現、
および area の零点が canonical flat top に一致することを一つに束ねる。
-/
structure LocalDecorationAreaDecompositionClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where

  area_vector_length :
    (localDecorationAreas D).length = D.lengths.length

  coordinate_area_exact :
    coordinateWeightedTranslation (arithmeticDecorationCoordinates D) =
      coordinateWeightedTranslation
          (canonicalFlatTopCoordinates P hPrimitive hReduced u D) +
        localWeightedDecorationArea P u D

  signed_defect_is_nat_area :
    localWeightedDecorationDefect P hPrimitive hReduced u D =
      (localWeightedDecorationArea P u D : ℤ)

  decoration_gap_area_exact :
    decorationGap P hPrimitive hReduced u D =
      2 * localWeightedDecorationArea P u D

  three_layer_area_exact :
    affineConst u.word =
      (3 ^ P.oddCount - 2 ^ P.oddCount) +
        boundaryGap P hPrimitive hReduced u D +
        2 * localWeightedDecorationArea P u D

  zero_area_iff_flat :
    localWeightedDecorationArea P u D = 0 ↔
      u = canonicalFlatTop P hPrimitive hReduced u D

/--
## Local Decoration Area Decomposition closure theorem

actual→flat top の residual は、各 actual record block の local Ferrers weighted area を
block-affine weights で集約した Nat potential の exact 2 倍である。
-/
theorem localDecorationAreaDecomposition_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    LocalDecorationAreaDecompositionClosed P hPrimitive hReduced u D := by
  refine {
    area_vector_length := localDecorationAreas_length D
    coordinate_area_exact := ?_
    signed_defect_is_nat_area := ?_
    decoration_gap_area_exact := ?_
    three_layer_area_exact := ?_
    zero_area_iff_flat := ?_
  }
  · exact coordinateWeightedTranslation_actual_eq_flat_add_localWeightedDecorationArea
      P hPrimitive hReduced u D
  · exact localWeightedDecorationDefect_eq_cast_localWeightedDecorationArea
      P hPrimitive hReduced u D
  · exact decorationGap_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D
  · exact affineConst_eq_absoluteBase_add_boundaryGap_add_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D
  · exact localWeightedDecorationArea_eq_zero_iff_source_eq_canonicalFlatTop
      P hPrimitive hReduced u D

end RecordFerrers
end Collatz2
