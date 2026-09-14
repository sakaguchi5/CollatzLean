import CollatzLean.Collatz3.Bridge.SurvivorRecordInteriorActual
import CollatzLean.Collatz3.Core.PrefixAffine
import CollatzLean.Collatz3.Canonical.REQ

/-!
# Collatz3 Bridge: actual survivor と critical completion の共通 affine 算術

actual infinite coefficient survivor の先頭 `m` odd steps と、その critical completion を
同じ座標で比較するための薄い bridge。

中心となる事実は次の三つ。

* critical completion は最後の exponent だけを延長するため、actual prefix と
  affine translation `B` を共有する。
* completion extra depth は survivor defect `δ_m` のちょうど `δ_m + 1`。
* completion の proper roof cut は actual survivor defect zero と exact に同値。

ここでは start residue の 2進 lift はまだ扱わない。後続
`SurvivorCompletionLift` で canonical start と actual start を比較する。
-/

namespace Collatz3

namespace Word

/--
word の最後の exponent は affine translation に影響しない。

`u ++ [a]` と `u ++ [b]` は、最後の odd step の `/2` 回数だけが異なる。
`affineConst` はその odd step に到達するまでの translation なので一致する。
-/
theorem affineConst_append_single_eq_append_single
    (u : Word)
    (a b : ℕ) :
    affineConst (u ++ [a]) = affineConst (u ++ [b]) := by
  rw [affineConst_append, affineConst_append]
  simp

end Word

namespace OddOrbit

open Bridge

/-- actual endpoint survivor code の critical completion word。 -/
def endpointCompletionCriticalWord
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Critical.CriticalWord (O.endpointSurvivorCode SInf m).1.length :=
  survivorCriticalCompletionWord
    (infinitePrefixDepth_pos SInf hm)
    (O.endpointSurvivorCode SInf m)

/-- completion critical word の underlying exponent word。 -/
def endpointCompletionWord
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) : Word :=
  (O.endpointCompletionCriticalWord SInf hm).1

/-- completion の canonical start。 -/
def endpointCompletionStart
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) : ℕ :=
  Word.canonicalStart (O.endpointCompletionWord SInf hm)

/-- completion の canonical odd endpoint。 -/
def endpointCompletionEnd
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) : ℕ :=
  Word.canonicalEnd (O.endpointCompletionWord SInf hm)

/-- actual endpoint depth から critical terminal までに追加する two-depth。 -/
def endpointCompletionExtraDepth
    (O : Collatz3.OddOrbit)
    (m : ℕ) : ℕ :=
  Critical.criticalTwoDepth m - infinitePrefixDepth O.exponent m

/-- completion word の odd-step 数は元の endpoint index `m`。 -/
theorem endpointCompletionWord_oddSteps
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Word.oddSteps (O.endpointCompletionWord SInf hm) = m := by
  change
    Word.oddSteps
        (survivorCriticalCompletionWord
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1 = m
  rw [
    (survivorCriticalCompletionWord
      (infinitePrefixDepth_pos SInf hm)
      (O.endpointSurvivorCode SInf m)).2.oddSteps_eq
  ]
  exact O.endpointSurvivorCode_length SInf m

/-- completion word の total two-depth は `criticalTwoDepth m`。 -/
theorem endpointCompletionWord_twoSteps
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Word.twoSteps (O.endpointCompletionWord SInf hm) =
      Critical.criticalTwoDepth m := by
  change
    Word.twoSteps
        (survivorCriticalCompletionWord
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1 =
      Critical.criticalTwoDepth m
  rw [
    (survivorCriticalCompletionWord
      (infinitePrefixDepth_pos SInf hm)
      (O.endpointSurvivorCode SInf m)).2.twoSteps_eq,
    O.endpointSurvivorCode_length SInf m
  ]

/-- completion canonical endpoint は奇数。 -/
theorem endpointCompletionEnd_odd
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Odd (O.endpointCompletionEnd SInf hm) := by
  exact Word.canonicalEnd_odd (O.endpointCompletionWord SInf hm)

/-- completion extra depth は常に正。 -/
theorem endpointCompletionExtraDepth_pos
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    0 < O.endpointCompletionExtraDepth m := by
  have hD := SInf.prefixDepth_le_beatty m
  unfold endpointCompletionExtraDepth Critical.criticalTwoDepth
  omega

/--
completion extra depth は survivor defect の exactly `+1`。

`K_m = beattyIndex m + 1` と `D_m + δ_m = beattyIndex m` の差を取っただけの式。
-/
theorem endpointCompletionExtraDepth_eq_defect_add_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.endpointCompletionExtraDepth m =
      infiniteSurvivorDefect O.exponent m + 1 := by
  have hD := SInf.prefixDepth_le_beatty m
  unfold endpointCompletionExtraDepth infiniteSurvivorDefect
    Critical.criticalTwoDepth
  omega

/--
critical completion と actual prefix は affine translation を共有する。

completion は最後の exponent だけを延長する。`affineConst` は最後の exponent の値に
依存しないため、同じ proper-prefix affine numerator `B_m` を持つ。
-/
theorem endpointCompletion_affineConst_eq_segmentWord
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    Word.affineConst (O.endpointCompletionWord SInf hm) =
      Word.affineConst (O.segmentWord 0 m) := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  have hBlocks : C.1.blocks = O.segmentWord 0 m := by
    rfl
  have hNe : C.1.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hD C.1
  have hRestore :
      C.1.blocks.dropLast ++ [C.1.blocks.getLast hNe] = C.1.blocks :=
    List.dropLast_append_getLast hNe
  change
    Word.affineConst
        (C.1.blocks.dropLast ++
          [parityLastBlock hD C.1 + survivorCriticalExtraDepth C]) =
      Word.affineConst (O.segmentWord 0 m)
  calc
    Word.affineConst
        (C.1.blocks.dropLast ++
          [parityLastBlock hD C.1 + survivorCriticalExtraDepth C])
        = Word.affineConst
            (C.1.blocks.dropLast ++ [parityLastBlock hD C.1]) := by
              exact Word.affineConst_append_single_eq_append_single
                C.1.blocks.dropLast
                (parityLastBlock hD C.1 + survivorCriticalExtraDepth C)
                (parityLastBlock hD C.1)
    _ = Word.affineConst C.1.blocks := by
          unfold parityLastBlock
          simpa using congrArg Word.affineConst hRestore
    _ = Word.affineConst (O.segmentWord 0 m) := by rw [hBlocks]

/-- actual first `m` odd steps の affine endpoint equation を prefix depth 座標で書く。 -/
theorem endpointSegment_req_equation
    (O : Collatz3.OddOrbit)
    (m : ℕ) :
    2 ^ infinitePrefixDepth O.exponent m * O.value m =
      3 ^ m * O.value 0 + Word.affineConst (O.segmentWord 0 m) := by
  have hRun := O.runsSegment 0 m
  have hRun' :
      Runs (O.segmentWord 0 m) (O.value 0) (O.value m) := by
    simpa using hRun
  have hEq :=
    (Word.endpointEquation_iff
      (O.segmentWord 0 m) (O.value 0) (O.value m)).1
      hRun'.endpointEquation
  have hDepth :=
    O.twoSteps_segmentWord_zero_eq_infinitePrefixDepth m
  have hOdd :=
    O.segmentWord_oddSteps 0 m
  simpa [hDepth, hOdd] using hEq

/-- critical completion canonical pair の affine endpoint equation。 -/
theorem endpointCompletion_req_equation
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    2 ^ Critical.criticalTwoDepth m * O.endpointCompletionEnd SInf hm =
      3 ^ m * O.endpointCompletionStart SInf hm +
        Word.affineConst (O.segmentWord 0 m) := by
  have hReq := Word.req_equation (O.endpointCompletionWord SInf hm)
  rw [
    O.endpointCompletionWord_twoSteps SInf hm,
    O.endpointCompletionWord_oddSteps SInf hm,
    O.endpointCompletion_affineConst_eq_segmentWord SInf hm
  ] at hReq
  simpa [endpointCompletionStart, endpointCompletionEnd] using hReq

/-- completion の canonical start はその full odd-endpoint modulus 未満。 -/
theorem endpointCompletionStart_lt_fullModulus
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hm : 0 < m) :
    O.endpointCompletionStart SInf hm <
      2 ^ (Critical.criticalTwoDepth m + 1) := by
  have h := Word.canonicalStart_lt_modulus (O.endpointCompletionWord SInf hm)
  rw [Word.oddEndpointModulus_eq, O.endpointCompletionWord_twoSteps SInf hm] at h
  simpa [endpointCompletionStart] using h

/--
completion の proper roof cut と actual survivor defect zero は exact に同値。

forward 方向は `8061fb1` で入った actual bridge。reverse 方向は completion profile height が
actual prefix depthそのもの、という同じ bridgeから戻す。
-/
theorem endpointCompletion_roofCut_iff_defect_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (haPos : 0 < a)
    (haLt : a < m) :
    Critical.IsRoofCut
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a ↔
      infiniteSurvivorDefect O.exponent a = 0 := by
  constructor
  · intro hRoof
    exact O.endpointCompletion_roofCut_defect_zero SInf hm hRoof
  · intro hZero
    let C := O.endpointSurvivorCode SInf m
    let hD := infinitePrefixDepth_pos SInf hm
    let H := survivorCriticalCompletionAdmissibleProfile hD C
    have hLen : C.1.length = m := by
      simp only [endpointSurvivorCode_length, C]
    have haC : a < C.1.length := by simpa [hLen] using haLt
    have hHeight :
        Critical.profileHeight H.1 a = C.1.sizeUpTo a := by
      exact survivorCompletion_profileHeight_eq_sizeUpTo hD C haC
    have hSize :
        C.1.sizeUpTo a = infinitePrefixDepth O.exponent a := by
      exact O.endpointSurvivorCode_sizeUpTo SInf m a (Nat.le_of_lt haLt)
    have hEq : infinitePrefixDepth O.exponent a = Critical.beattyIndex a := by
      unfold infiniteSurvivorDefect at hZero
      have hLe := SInf.prefixDepth_le_beatty a
      omega
    refine ⟨haPos, ?_, ?_⟩
    · simpa [C, hD, H, hLen] using haLt
    · change Critical.profileHeight H.1 a = Critical.beattyIndex a
      rw [hHeight, hSize]
      exact hEq

end OddOrbit
end Collatz3
