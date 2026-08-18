import CollatzLean.Collatz2.CSTMicro.FirstFailureProvenance
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.NormalizedDefectCrossing

/-!
# General CST: normalized Ferrers cocycle from A boundary to B first failure

`NormalizedDefectCrossing` では actual first failure edge に対して

  q_lower < 0 <= q_upper,
  q_upper = q_lower + D

を得た。

このファイルでは normalized defect

  q(v) = normalizedSeparationDefectInt v

を Ferrers chain 全体の integer cocycle として扱う。

一つの adjacent Ferrers step では

* no-carry : q は strict に減少する
* carry    : q は canonical Farey residue だけ exact に変化する

ことを generic first-passage edge で証明する。

最後に `FirstFailureProvenance` と結合し、

  q_upper
    = q_boundary + prefixDelta + failureResidue

という A boundary -> B first failure の exact identity を得る。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. safety / failure と normalized q の符号 -/

/-- safe first-passage word の normalized defect は strict negative。 -/
theorem normalizedSeparationDefectInt_neg_of_wordPureSeparation
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hSafe : WordPureSeparation v) :
    normalizedSeparationDefectInt v < 0 := by
  have hDef : wordSeparationDefectInt v < 0 := by
    unfold WordPureSeparation at hSafe
    have hInt :
        (affineConst v : ℤ) <
          (wordTerminalGap v : ℤ) *
            (leastRepresentative v : ℤ) := by
      exact_mod_cast hSafe
    unfold wordSeparationDefectInt
    linarith
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      v hFP.2.2
  rw [hFactor] at hDef
  have hModPos : 0 < (parityModulus v : ℤ) := by
    exact_mod_cast parityModulus_pos v
  by_contra hnot
  have hq : 0 ≤ normalizedSeparationDefectInt v := by
    omega
  have hprod :
      0 ≤ (parityModulus v : ℤ) * normalizedSeparationDefectInt v :=
    mul_nonneg (le_of_lt hModPos) hq
  linarith

/-- failure first-passage word の normalized defect は nonnegative。 -/
theorem normalizedSeparationDefectInt_nonneg_of_wordPureSeparation_failure
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hFail : ¬ WordPureSeparation v) :
    0 ≤ normalizedSeparationDefectInt v := by
  have hNat :
      wordTerminalGap v * leastRepresentative v ≤ affineConst v := by
    unfold WordPureSeparation at hFail
    omega
  have hDef : 0 ≤ wordSeparationDefectInt v := by
    unfold wordSeparationDefectInt
    have hInt :
        (wordTerminalGap v : ℤ) *
            (leastRepresentative v : ℤ) ≤
          (affineConst v : ℤ) := by
      exact_mod_cast hNat
    linarith
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      v hFP.2.2
  rw [hFactor] at hDef
  have hModPos : 0 < (parityModulus v : ℤ) := by
    exact_mod_cast parityModulus_pos v
  by_contra hnot
  have hq : normalizedSeparationDefectInt v < 0 := by
    omega
  have hprod :
      (parityModulus v : ℤ) * normalizedSeparationDefectInt v < 0 :=
    mul_neg_of_pos_of_neg hModPos hq
  linarith

/-! ## 2. generic adjacent step law -/

namespace AdjacentFerrersSwap

/--
canonical Farey packet の gap coordinate `G` は、lower word が contracting なら
word-level terminal gap の integer cast に一致する。
-/
theorem fareyPacket_G_eq_wordTerminalGap
    (S : AdjacentFerrersSwap)
    (hContract : CoefficientContracting S.lowerWord) :
    S.toFareyCellPacket.G =
      (wordTerminalGap S.lowerWord : ℤ) := by
  have hContract' := hContract
  unfold CoefficientContracting at hContract'
  rw [S.lowerWord_oddCount, S.lowerWord_length] at hContract'
  have hle : 3 ^ S.oddTotal ≤ S.modulus := by
    unfold AdjacentFerrersSwap.modulus
    exact Nat.le_of_lt hContract'
  change
    (2 : ℤ) ^ S.length - (3 : ℤ) ^ S.oddTotal =
      (wordTerminalGap S.lowerWord : ℤ)
  rw [S.wordTerminalGap_lowerWord]
  rw [Nat.cast_sub hle]
  simp [AdjacentFerrersSwap.modulus]

/--
任意の contracting adjacent cell で carry jump は
common modulus と canonical Farey residue の積に exact factor する。

first-failure 性は不要。
-/
theorem carryCellJumpInt_eq_modulus_mul_fareyResidue
    (S : AdjacentFerrersSwap)
    (hContract : CoefficientContracting S.lowerWord) :
    S.carryCellJumpInt =
      (S.modulus : ℤ) * S.toFareyCellPacket.residue := by
  let P := S.toFareyCellPacket
  have hG :
      P.G = (wordTerminalGap S.lowerWord : ℤ) := by
    simpa [P] using S.fareyPacket_G_eq_wordTerminalGap hContract
  have hTwo :
      (2 : ℤ) ^ S.fareyTailDepth * P.residue =
        P.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent := by
    simpa [P, AdjacentFerrersSwap.toFareyCellPacket] using
      P.twoPow_mul_residue
  have hComp :
      (S.carryComplement : ℤ) =
        (2 : ℤ) ^ S.position * (S.fareyH : ℤ) := by
    exact_mod_cast S.carryComplement_eq_twoPow_mul_fareyH
  have hDeltaB :
      (S.deltaB : ℤ) =
        (2 : ℤ) ^ S.position *
          (3 : ℤ) ^ S.fareyRightExponent := by
    unfold AdjacentFerrersSwap.deltaB
      AdjacentFerrersSwap.fareyRightExponent
    push_cast
    rfl
  calc
    S.carryCellJumpInt
        =
      P.G *
          ((2 : ℤ) ^ S.position * (S.fareyH : ℤ)) -
        (2 : ℤ) ^ S.position *
          (3 : ℤ) ^ S.fareyRightExponent := by
            unfold AdjacentFerrersSwap.carryCellJumpInt
            rw [hComp, ← hG, hDeltaB]
    _ =
      (2 : ℤ) ^ S.position *
        (P.G * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent) := by
            ring
    _ =
      (2 : ℤ) ^ S.position *
        ((2 : ℤ) ^ S.fareyTailDepth * P.residue) := by
          rw [← hTwo]
    _ =
      (S.modulus : ℤ) * P.residue := by
        unfold AdjacentFerrersSwap.modulus
        rw [S.length_eq_position_add_fareyTailDepth, pow_add]
        push_cast
        ring
    _ =
      (S.modulus : ℤ) * S.toFareyCellPacket.residue := by
        rfl

/-- no-carry adjacent move は normalized q を strict に下げる。 -/
theorem normalized_upper_lt_lower_of_noCarry
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord)
    (hNoCarry : S.NoCarry) :
    normalizedSeparationDefectInt S.upperWord <
      normalizedSeparationDefectInt S.lowerWord := by
  have hUpperContract : CoefficientContracting S.upperWord := by
    have h := hLowerFP.2.2
    unfold CoefficientContracting at h ⊢
    simpa using h
  have hLowerFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.lowerWord hLowerFP.2.2
  have hUpperFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.upperWord hUpperContract
  rw [S.parityModulus_lowerWord] at hLowerFactor
  rw [S.parityModulus_upperWord] at hUpperFactor
  have hB := S.lower_affineConst_eq_upper_add_deltaB
  have hR := S.upperR_eq_add_of_noCarry hNoCarry
  have hBz :
      (affineConst S.lowerWord : ℤ) =
        (affineConst S.upperWord : ℤ) + (S.deltaB : ℤ) := by
    exact_mod_cast hB
  have hRz :
      (S.upperR : ℤ) =
        (S.lowerR : ℤ) + (S.deltaR : ℤ) := by
    exact_mod_cast hR
  have hDeltaBPos : 0 < (S.deltaB : ℤ) := by
    unfold AdjacentFerrersSwap.deltaB
    positivity
  have hDefLt :
      wordSeparationDefectInt S.upperWord <
        wordSeparationDefectInt S.lowerWord := by
    unfold wordSeparationDefectInt
    change
      (affineConst S.upperWord : ℤ) -
          (wordTerminalGap S.upperWord : ℤ) * (S.upperR : ℤ) <
        (affineConst S.lowerWord : ℤ) -
          (wordTerminalGap S.lowerWord : ℤ) * (S.lowerR : ℤ)
    rw [← S.wordTerminalGap_eq]
    rw [hBz, hRz]
    have hGapNonneg :
        0 ≤ (wordTerminalGap S.lowerWord : ℤ) := by
      positivity
    have hDeltaRNonneg : 0 ≤ (S.deltaR : ℤ) := by
      positivity
    nlinarith
  rw [hUpperFactor, hLowerFactor] at hDefLt
  have hModPos : 0 < (S.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  nlinarith

/--
carry adjacent move は normalized q を canonical Farey residue だけ exact に増減する。

first-passage lower を仮定すれば terminal contraction は upper にも共通なので、
raw defect jump `carryCellJumpInt` を common modulus で割って得られる。
-/
theorem normalized_upper_eq_lower_add_fareyResidue_of_hasCarry
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord)
    (hCarry : S.HasCarry) :
    normalizedSeparationDefectInt S.upperWord =
      normalizedSeparationDefectInt S.lowerWord +
        S.toFareyCellPacket.residue := by
  have hUpperContract : CoefficientContracting S.upperWord := by
    have h := hLowerFP.2.2
    unfold CoefficientContracting at h ⊢
    simpa using h
  have hJump :=
    S.upper_defect_sub_lower_defect_eq_carryCellJumpInt_of_hasCarry
      hCarry
  have hLowerFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.lowerWord hLowerFP.2.2
  have hUpperFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      S.upperWord hUpperContract
  rw [S.parityModulus_lowerWord] at hLowerFactor
  rw [S.parityModulus_upperWord] at hUpperFactor
  have hFareyJump :=
    S.carryCellJumpInt_eq_modulus_mul_fareyResidue
      hLowerFP.2.2
  rw [hUpperFactor, hLowerFactor, hFareyJump] at hJump
  have hModPos : 0 < (S.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  nlinarith

end AdjacentFerrersSwap

namespace FerrersStep

/-- 一つの Ferrers move の endpoints 間の normalized q の signed increment。 -/
def normalizedStepDelta
    (lower upper : ParityWord) : ℤ :=
  normalizedSeparationDefectInt upper -
    normalizedSeparationDefectInt lower

/-- no-carry Ferrers step の normalized increment は strict negative。 -/
theorem normalizedStepDelta_neg_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hNoCarry : S.edge.NoCarry) :
    normalizedStepDelta lower upper < 0 := by
  have hEdgeFP : IsFirstPassageWord S.edge.lowerWord := by
    simpa [S.lower_eq] using hLowerFP
  have h :=
    S.edge.normalized_upper_lt_lower_of_noCarry hEdgeFP hNoCarry
  have hLower :
      normalizedSeparationDefectInt lower =
        normalizedSeparationDefectInt S.edge.lowerWord :=
    congrArg normalizedSeparationDefectInt S.lower_eq
  have hUpper :
      normalizedSeparationDefectInt upper =
        normalizedSeparationDefectInt S.edge.upperWord :=
    congrArg normalizedSeparationDefectInt S.upper_eq
  unfold normalizedStepDelta
  rw [hLower, hUpper]
  omega

/-- carry Ferrers step の normalized increment は canonical Farey residue。 -/
theorem normalizedStepDelta_eq_fareyResidue_of_hasCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hCarry : S.edge.HasCarry) :
    normalizedStepDelta lower upper =
      S.edge.toFareyCellPacket.residue := by
  have hEdgeFP : IsFirstPassageWord S.edge.lowerWord := by
    simpa [S.lower_eq] using hLowerFP
  have h :=
    S.edge.normalized_upper_eq_lower_add_fareyResidue_of_hasCarry
      hEdgeFP hCarry
  have hLower :
      normalizedSeparationDefectInt lower =
        normalizedSeparationDefectInt S.edge.lowerWord :=
    congrArg normalizedSeparationDefectInt S.lower_eq
  have hUpper :
      normalizedSeparationDefectInt upper =
        normalizedSeparationDefectInt S.edge.upperWord :=
    congrArg normalizedSeparationDefectInt S.upper_eq
  unfold normalizedStepDelta
  rw [hLower, hUpper]
  linarith

/--
first-passage Ferrers step の normalized law。
no-carry なら negative increment、carry なら exact Farey residue。
-/
theorem normalizedStepDelta_law
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    (S.edge.NoCarry ∧ normalizedStepDelta lower upper < 0) ∨
      (S.edge.HasCarry ∧
        normalizedStepDelta lower upper =
          S.edge.toFareyCellPacket.residue) := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · exact
      Or.inl
        ⟨hNo,
          S.normalizedStepDelta_neg_of_noCarry hLowerFP hNo⟩
  · exact
      Or.inr
        ⟨hCarry,
          S.normalizedStepDelta_eq_fareyResidue_of_hasCarry
            hLowerFP hCarry⟩

end FerrersStep

/-! ## 3. chain-level cocycle -/

namespace FerrersChain

/-- Ferrers chain 全体の normalized signed increment。 -/
def normalizedDelta
    {start finish : ParityWord}
    (_C : FerrersChain start finish) : ℤ :=
  normalizedSeparationDefectInt finish -
    normalizedSeparationDefectInt start

/-- normalized q は chain increment を exact に telescope する。 -/
theorem normalized_finish_eq_start_add_delta
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    normalizedSeparationDefectInt finish =
      normalizedSeparationDefectInt start + C.normalizedDelta := by
  unfold normalizedDelta
  ring

end FerrersChain

/-! ## 4. A boundary -> B first failure exact cocycle -/

namespace FirstFailureProvenance

/-- A-side boundary の normalized q は strict negative。 -/
theorem boundary_normalized_neg
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.boundary < 0 := by
  exact
    normalizedSeparationDefectInt_neg_of_wordPureSeparation
      P.boundary_isBoundary.1 P.safePrefixChain.start_safe

/-- integer coordinate なので A-side boundary は少なくとも `-1` 以下。 -/
theorem boundary_normalized_le_neg_one
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.boundary ≤ -1 := by
  have h := P.boundary_normalized_neg
  omega

/-- first failure 直前の lower normalized q は strict negative。 -/
theorem lower_normalized_neg
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.lower < 0 := by
  exact
    normalizedSeparationDefectInt_neg_of_wordPureSeparation
      P.lower_firstPassage P.lower_safe

/-- first failure upper normalized q は nonnegative。 -/
theorem upper_normalized_nonneg
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    0 ≤ normalizedSeparationDefectInt P.upper := by
  exact
    normalizedSeparationDefectInt_nonneg_of_wordPureSeparation_failure
      P.upper_firstPassage P.upper_failure

/-- A boundary から first failure lower までの exact prefix cocycle。 -/
theorem lower_eq_boundary_add_prefixDelta
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.lower =
      normalizedSeparationDefectInt P.boundary +
        P.safePrefixChain.toFerrersChain.normalizedDelta := by
  exact P.safePrefixChain.toFerrersChain.normalized_finish_eq_start_add_delta

/-- first failure では normalized q が exact に Farey residue だけ増える。 -/
theorem upper_eq_lower_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.upper =
      normalizedSeparationDefectInt P.lower +
        P.failureStep.edge.toFareyCellPacket.residue := by
  have hEdgeFP :
      IsFirstPassageWord P.failureStep.edge.lowerWord := by
    simpa [P.failureStep.lower_eq] using P.lower_firstPassage
  have hEdge :=
    P.failureStep.edge.normalized_upper_eq_lower_add_fareyResidue_of_hasCarry
      hEdgeFP
      P.failure_hasCarry
  have hLower :
      normalizedSeparationDefectInt P.lower =
        normalizedSeparationDefectInt P.failureStep.edge.lowerWord :=
    congrArg normalizedSeparationDefectInt P.failureStep.lower_eq
  have hUpper :
      normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.failureStep.edge.upperWord :=
    congrArg normalizedSeparationDefectInt P.failureStep.upper_eq
  calc
    normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.failureStep.edge.upperWord :=
      hUpper
    _ =
        normalizedSeparationDefectInt P.failureStep.edge.lowerWord +
          P.failureStep.edge.toFareyCellPacket.residue :=
      hEdge
    _ =
        normalizedSeparationDefectInt P.lower +
          P.failureStep.edge.toFareyCellPacket.residue := by
      rw [← hLower]

/--
A boundary から B first failure upper までの exact cocycle。

  q_upper = q_boundary + prefixDelta + D_failure.
-/
theorem upper_eq_boundary_add_prefixDelta_add_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.upper =
      normalizedSeparationDefectInt P.boundary +
        P.safePrefixChain.toFerrersChain.normalizedDelta +
        P.failureStep.edge.toFareyCellPacket.residue := by
  calc
    normalizedSeparationDefectInt P.upper
        =
      normalizedSeparationDefectInt P.lower +
        P.failureStep.edge.toFareyCellPacket.residue :=
          P.upper_eq_lower_add_failureResidue
    _ =
      (normalizedSeparationDefectInt P.boundary +
          P.safePrefixChain.toFerrersChain.normalizedDelta) +
        P.failureStep.edge.toFareyCellPacket.residue := by
          rw [P.lower_eq_boundary_add_prefixDelta]
    _ =
      normalizedSeparationDefectInt P.boundary +
        P.safePrefixChain.toFerrersChain.normalizedDelta +
        P.failureStep.edge.toFareyCellPacket.residue := by
          ring

/-- first failure residue は strict positive。 -/
theorem failureResidue_pos
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    0 < P.failureStep.edge.toFareyCellPacket.residue := by
  have hLower := P.lower_normalized_neg
  have hUpper := P.upper_normalized_nonneg
  have hEq := P.upper_eq_lower_add_failureResidue
  linarith

/-- first failure carry は直前に残った negative safety を少なくとも跨ぐ。 -/
theorem neg_lower_le_failureResidue
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    -normalizedSeparationDefectInt P.lower ≤
      P.failureStep.edge.toFareyCellPacket.residue := by
  have hUpper := P.upper_normalized_nonneg
  have hEq := P.upper_eq_lower_add_failureResidue
  linarith

/-- boundary から first failure までの total normalized gain は strict positive。 -/
theorem total_gain_pos
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    0 <
      P.safePrefixChain.toFerrersChain.normalizedDelta +
        P.failureStep.edge.toFareyCellPacket.residue := by
  have hBoundary := P.boundary_normalized_neg
  have hUpper := P.upper_normalized_nonneg
  have hEq := P.upper_eq_boundary_add_prefixDelta_add_failureResidue
  linarith

/--
A/B 接続を一つの packet にまとめる。

boundary は integer strip の負側にあり、safe prefix を通った後、
canonical failure residue が初めて zero を跨ぐ。
-/
theorem boundary_to_firstFailure_cocycle_packet
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    normalizedSeparationDefectInt P.boundary ≤ -1 ∧
      normalizedSeparationDefectInt P.lower < 0 ∧
      0 ≤ normalizedSeparationDefectInt P.upper ∧
      normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.boundary +
          P.safePrefixChain.toFerrersChain.normalizedDelta +
          P.failureStep.edge.toFareyCellPacket.residue ∧
      0 < P.failureStep.edge.toFareyCellPacket.residue ∧
      0 <
        P.safePrefixChain.toFerrersChain.normalizedDelta +
          P.failureStep.edge.toFareyCellPacket.residue := by
  exact
    ⟨P.boundary_normalized_le_neg_one,
      P.lower_normalized_neg,
      P.upper_normalized_nonneg,
      P.upper_eq_boundary_add_prefixDelta_add_failureResidue,
      P.failureResidue_pos,
      P.total_gain_pos⟩

end FirstFailureProvenance

end CSTMicro
end Collatz2
