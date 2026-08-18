import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FirstFailureFareyExtraction

/-!
# General CST: B first-failure normalized defect crossing

`FirstFailureFareyExtraction` までで B の actual first failure は

  carryCellJumpInt = 2^k * D,
  0 < D < G

という bounded Farey cell を持つ。

このファイルでは word-level signed defect

  defect = B - G * R

が terminal-contracting word で parity modulus `2^k` の倍数になることを ordinary integer に戻し、
その quotient を canonical affine endpoint と start representative の差

  q = endpoint(R) - R

として定義する。

B first failure では

  q_lower < 0 ≤ q_upper,
  q_upper = q_lower + D,
  q_upper < m,
  q_upper < D,
  0 < D < G

を同時に得る。これが後段 weighted-rank bridge へ渡す normalized crossing strip である。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. normalized signed defect -/

/--
least parity representative `R` を whole affine equation に代入して得る
canonical affine endpoint。

parity congruenceにより numerator は `2^k` で exact に割り切れる。
-/
def representativeAffineEndpoint (v : ParityWord) : ℕ :=
  (3 ^ oddCount v * leastRepresentative v + affineConst v) /
    parityModulus v

/--
canonical parity representative を affine equation に入れた numerator は
parity modulus で 0 mod。
-/
theorem parityNumerator_mod_eq_zero
    (v : ParityWord) :
    (3 ^ oddCount v * leastRepresentative v + affineConst v) %
        parityModulus v = 0 := by
  haveI : NeZero (parityModulus v) :=
    ⟨Nat.ne_of_gt (parityModulus_pos v)⟩
  have hc := leastRepresentative_cast v
  have hs := parityStartClass_spec v
  rw [← hc] at hs
  have hcast :
      (((3 ^ oddCount v * leastRepresentative v + affineConst v : ℕ)) :
          ZMod (parityModulus v)) = 0 := by
    push_cast
    simpa using hs
  calc
    (3 ^ oddCount v * leastRepresentative v + affineConst v) %
        parityModulus v
        =
      ((((3 ^ oddCount v * leastRepresentative v + affineConst v : ℕ)) :
          ZMod (parityModulus v)).val) := by
        exact
          (ZMod.val_natCast
            (parityModulus v)
            (3 ^ oddCount v * leastRepresentative v + affineConst v)).symm
    _ =
      ZMod.val (0 : ZMod (parityModulus v)) := by
        exact congrArg ZMod.val hcast
    _ = 0 := by
      exact ZMod.val_zero

/-- canonical affine endpoint の defining equation。 -/
theorem parityModulus_mul_representativeAffineEndpoint
    (v : ParityWord) :
    parityModulus v * representativeAffineEndpoint v =
      3 ^ oddCount v * leastRepresentative v + affineConst v := by
  have hdiv :=
    Nat.mod_add_div
      (3 ^ oddCount v * leastRepresentative v + affineConst v)
      (parityModulus v)
  rw [parityNumerator_mod_eq_zero v] at hdiv
  simp only [zero_add] at hdiv
  simpa [representativeAffineEndpoint] using hdiv

/--
`defect / 2^k` の canonical integer version。

signed division を直接使わず、affine endpoint と least representative の差
として持つ。
-/
def normalizedSeparationDefectInt (v : ParityWord) : ℤ :=
  (representativeAffineEndpoint v : ℤ) -
    (leastRepresentative v : ℤ)

/--
terminal contracting word では signed defect は exact に

  defect = 2^k * normalizedDefect

へ factor する。
-/
theorem wordSeparationDefectInt_eq_modulus_mul_normalized
    (v : ParityWord)
    (hContract : CoefficientContracting v) :
    wordSeparationDefectInt v =
      (parityModulus v : ℤ) * normalizedSeparationDefectInt v := by
  have hEndpointNat := parityModulus_mul_representativeAffineEndpoint v
  have hEndpointInt :
      (parityModulus v : ℤ) * (representativeAffineEndpoint v : ℤ) =
        ((3 ^ oddCount v : ℕ) : ℤ) * (leastRepresentative v : ℤ) +
          (affineConst v : ℤ) := by
    exact_mod_cast hEndpointNat
  have hContract' := hContract
  unfold CoefficientContracting at hContract'
  have hle :
      3 ^ oddCount v ≤ 2 ^ v.length :=
    Nat.le_of_lt hContract'
  have hGap :
      (wordTerminalGap v : ℤ) =
        (parityModulus v : ℤ) - ((3 ^ oddCount v : ℕ) : ℤ) := by
    unfold wordTerminalGap parityModulus
    rw [Nat.cast_sub hle]
  unfold wordSeparationDefectInt normalizedSeparationDefectInt
  rw [hGap]
  calc
    (affineConst v : ℤ) -
          ((parityModulus v : ℤ) - ((3 ^ oddCount v : ℕ) : ℤ)) *
            (leastRepresentative v : ℤ)
        =
      (((3 ^ oddCount v : ℕ) : ℤ) * (leastRepresentative v : ℤ) +
          (affineConst v : ℤ)) -
        (parityModulus v : ℤ) * (leastRepresentative v : ℤ) := by
          ring
    _ =
      (parityModulus v : ℤ) * (representativeAffineEndpoint v : ℤ) -
        (parityModulus v : ℤ) * (leastRepresentative v : ℤ) := by
          rw [← hEndpointInt]
    _ =
      (parityModulus v : ℤ) *
        ((representativeAffineEndpoint v : ℤ) -
          (leastRepresentative v : ℤ)) := by
            ring

/-! ## 2. B first-failure strip coordinates -/

namespace FirstFailureEdge

/-- first-failure lower edge word は first-passage。 -/
theorem edge_lower_firstPassage
    (F : FirstFailureEdge) :
    IsFirstPassageWord F.step.edge.lowerWord := by
  rw [← F.step.lower_eq]
  exact F.lower_firstPassage

/-- first-failure upper edge word は first-passage。 -/
theorem edge_upper_firstPassage
    (F : FirstFailureEdge) :
    IsFirstPassageWord F.step.edge.upperWord := by
  rw [← F.step.upper_eq]
  exact F.upper_firstPassage

/-- first failure の lower normalized defect は strict negative。 -/
theorem lower_normalizedSeparationDefectInt_neg
    (F : FirstFailureEdge) :
    normalizedSeparationDefectInt F.step.edge.lowerWord < 0 := by
  have hDef :
      wordSeparationDefectInt F.step.edge.lowerWord < 0 := by
    rw [← F.step.lower_eq]
    exact F.lower_wordSeparationDefectInt_neg
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.lowerWord F.edge_lower_firstPassage.2.2
  rw [hFactor] at hDef
  have hModPos :
      0 < (parityModulus F.step.edge.lowerWord : ℤ) := by
    exact_mod_cast parityModulus_pos F.step.edge.lowerWord
  by_contra hnot
  have hq :
      0 ≤ normalizedSeparationDefectInt F.step.edge.lowerWord := by
    omega
  have hprod :
      0 ≤
        (parityModulus F.step.edge.lowerWord : ℤ) *
          normalizedSeparationDefectInt F.step.edge.lowerWord :=
    mul_nonneg (le_of_lt hModPos) hq
  linarith

/-- first failure の upper normalized defect は nonnegative。 -/
theorem upper_normalizedSeparationDefectInt_nonneg
    (F : FirstFailureEdge) :
    0 ≤ normalizedSeparationDefectInt F.step.edge.upperWord := by
  have hDef :
      0 ≤ wordSeparationDefectInt F.step.edge.upperWord := by
    rw [← F.step.upper_eq]
    exact F.upper_wordSeparationDefectInt_nonneg
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.upperWord F.edge_upper_firstPassage.2.2
  rw [hFactor] at hDef
  have hModPos :
      0 < (parityModulus F.step.edge.upperWord : ℤ) := by
    exact_mod_cast parityModulus_pos F.step.edge.upperWord
  by_contra hnot
  have hq :
      normalizedSeparationDefectInt F.step.edge.upperWord < 0 := by
    omega
  have hprod :
      (parityModulus F.step.edge.upperWord : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord < 0 :=
    mul_neg_of_pos_of_neg hModPos hq
  linarith

/-- upper first-passage affine numerator の sharp linear-in-`m` bound。 -/
theorem upper_affineConst_le_oddTotal_mul_threePow
    (F : FirstFailureEdge) :
    affineConst F.step.edge.upperWord ≤
      F.step.edge.oddTotal * 3 ^ F.step.edge.oddTotal := by
  let P :=
    firstPassagePathOfWord
      F.step.edge.upperWord F.edge_upper_firstPassage
  have h := P.affineConst_le_endpointOddCount_mul_threePow
  simpa [P, firstPassagePathOfWord, FirstPassagePath.endpointOddCount] using h

/-- first-failure edge の odd total は正。 -/
theorem edge_oddTotal_pos
    (F : FirstFailureEdge) :
    0 < F.step.edge.oddTotal := by
  unfold AdjacentFerrersSwap.oddTotal
  omega

/-- first-passage upper edge の terminal coefficient は contracting。 -/
theorem upper_threePow_lt_modulus
    (F : FirstFailureEdge) :
    3 ^ F.step.edge.oddTotal < F.step.edge.modulus := by
  have h := F.edge_upper_firstPassage.2.2
  unfold CoefficientContracting at h
  simpa [AdjacentFerrersSwap.modulus] using h

/-- upper affine numerator は `m * 2^k` より strict に小さい。 -/
theorem upper_affineConst_lt_oddTotal_mul_modulus
    (F : FirstFailureEdge) :
    affineConst F.step.edge.upperWord <
      F.step.edge.oddTotal * F.step.edge.modulus := by
  have hB := F.upper_affineConst_le_oddTotal_mul_threePow
  have hPow := F.upper_threePow_lt_modulus
  have hm := F.edge_oddTotal_pos
  have hmul :
      F.step.edge.oddTotal * 3 ^ F.step.edge.oddTotal <
        F.step.edge.oddTotal * F.step.edge.modulus :=
    (Nat.mul_lt_mul_left hm).2 hPow
  exact lt_of_le_of_lt hB hmul

/-- first failure の upper normalized defect は endpoint odd count より小さい。 -/
theorem upper_normalizedSeparationDefectInt_lt_oddTotal
    (F : FirstFailureEdge) :
    normalizedSeparationDefectInt F.step.edge.upperWord <
      (F.step.edge.oddTotal : ℤ) := by
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.upperWord F.edge_upper_firstPassage.2.2
  rw [F.step.edge.parityModulus_upperWord] at hFactor
  have hDefLeB :
      wordSeparationDefectInt F.step.edge.upperWord ≤
        (affineConst F.step.edge.upperWord : ℤ) := by
    unfold wordSeparationDefectInt
    have hNonneg :
        0 ≤
          (wordTerminalGap F.step.edge.upperWord : ℤ) *
            (leastRepresentative F.step.edge.upperWord : ℤ) := by
      positivity
    linarith
  have hMqLe :
      (F.step.edge.modulus : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord ≤
        (affineConst F.step.edge.upperWord : ℤ) := by
    rw [← hFactor]
    exact hDefLeB
  have hBltNat := F.upper_affineConst_lt_oddTotal_mul_modulus
  have hBlt :
      (affineConst F.step.edge.upperWord : ℤ) <
        (F.step.edge.oddTotal : ℤ) * (F.step.edge.modulus : ℤ) := by
    exact_mod_cast hBltNat
  have hModPos : 0 < (F.step.edge.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  have hMulLt :
      (F.step.edge.modulus : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord <
        (F.step.edge.modulus : ℤ) * (F.step.edge.oddTotal : ℤ) := by
    calc
      (F.step.edge.modulus : ℤ) *
            normalizedSeparationDefectInt F.step.edge.upperWord
          ≤ (affineConst F.step.edge.upperWord : ℤ) := hMqLe
      _ <
          (F.step.edge.oddTotal : ℤ) * (F.step.edge.modulus : ℤ) := hBlt
      _ =
          (F.step.edge.modulus : ℤ) * (F.step.edge.oddTotal : ℤ) := by
            ring
  exact (Int.mul_lt_mul_left hModPos).mp hMulLt

/-- upper normalized defect は path length よりも小さい。 -/
theorem upper_normalizedSeparationDefectInt_lt_length
    (F : FirstFailureEdge) :
    normalizedSeparationDefectInt F.step.edge.upperWord <
      (F.step.edge.length : ℤ) := by
  have hq := F.upper_normalizedSeparationDefectInt_lt_oddTotal
  have hmNat : F.step.edge.oddTotal ≤ F.step.edge.length := by
    have h := oddCount_le_length F.step.edge.upperWord
    simpa using h
  have hm :
      (F.step.edge.oddTotal : ℤ) ≤ (F.step.edge.length : ℤ) := by
    exact_mod_cast hmNat
  exact lt_of_lt_of_le hq hm

/--
upper defect equation を ordinary integer strip coordinate で書き直す。
Farey data を使わないため、B first-failure の normalized layer に置く。
-/
theorem upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized
    (F : FirstFailureEdge) :
    (affineConst F.step.edge.upperWord : ℤ) =
      (wordTerminalGap F.step.edge.upperWord : ℤ) *
          (F.step.edge.upperR : ℤ) +
        (F.step.edge.modulus : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord := by
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.upperWord F.edge_upper_firstPassage.2.2
  rw [F.step.edge.parityModulus_upperWord] at hFactor
  unfold wordSeparationDefectInt at hFactor
  change
    (affineConst F.step.edge.upperWord : ℤ) =
      (wordTerminalGap F.step.edge.upperWord : ℤ) *
          (leastRepresentative F.step.edge.upperWord : ℤ) +
        (F.step.edge.modulus : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord
  simpa [AdjacentFerrersSwap.upperR] using (by
    linarith [hFactor] :
      (affineConst F.step.edge.upperWord : ℤ) =
        (wordTerminalGap F.step.edge.upperWord : ℤ) *
            (leastRepresentative F.step.edge.upperWord : ℤ) +
          (F.step.edge.modulus : ℤ) *
            normalizedSeparationDefectInt F.step.edge.upperWord)

end FirstFailureEdge

/-! ## 3. Farey jump と normalized crossing の結合 -/

namespace FirstFailureFareyData

/-- actual carry jump は common modulus `2^k` と Farey residue の積。 -/
theorem carryCellJumpInt_eq_modulus_mul_residue
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    F.step.edge.carryCellJumpInt =
      (F.step.edge.modulus : ℤ) * D.farey.residue := by
  rw [D.carryCellJumpInt_eq_twoPow_mul_twoPow_mul_residue]
  change
    (2 : ℤ) ^ D.farey.i *
          ((2 : ℤ) ^ D.farey.d * D.farey.residue) =
      (2 : ℤ) ^ F.step.edge.length * D.farey.residue
  rw [← D.k_eq_length, D.farey.k_eq, pow_add]
  ring

/-- normalized defect は一つの actual first-failure cell で exact に `D` 増える。 -/
theorem normalizedSeparationDefectInt_upper_eq_lower_add_residue
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    normalizedSeparationDefectInt F.step.edge.upperWord =
      normalizedSeparationDefectInt F.step.edge.lowerWord +
        D.farey.residue := by
  have hJump :=
    F.step.edge.upper_defect_sub_lower_defect_eq_carryCellJumpInt_of_hasCarry
      F.hasCarry
  have hUpperFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.upperWord F.edge_upper_firstPassage.2.2
  have hLowerFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      F.step.edge.lowerWord F.edge_lower_firstPassage.2.2
  rw [F.step.edge.parityModulus_upperWord] at hUpperFactor
  rw [F.step.edge.parityModulus_lowerWord] at hLowerFactor
  rw [hUpperFactor, hLowerFactor,
    D.carryCellJumpInt_eq_modulus_mul_residue] at hJump
  have hModPos : 0 < (F.step.edge.modulus : ℤ) := by
    unfold AdjacentFerrersSwap.modulus
    positivity
  nlinarith

/-- first failure では small upper coordinate は Farey jump `D` より小さい。 -/
theorem upper_normalizedSeparationDefectInt_lt_residue
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    normalizedSeparationDefectInt F.step.edge.upperWord <
      D.farey.residue := by
  have hLower := F.lower_normalizedSeparationDefectInt_neg
  have hJump := D.normalizedSeparationDefectInt_upper_eq_lower_add_residue
  nlinarith

/--
first failure の normalized crossing strip。

  q_lower < 0,
  0 ≤ q_upper < m,
  q_upper = q_lower + D,
  q_upper < D.
-/
theorem normalized_crossing_strip
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
    let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
    qLower < 0 ∧
      0 ≤ qUpper ∧
      qUpper < (D.farey.m : ℤ) ∧
      qUpper = qLower + D.farey.residue ∧
      qUpper < D.farey.residue := by
  dsimp
  refine ⟨F.lower_normalizedSeparationDefectInt_neg,
    F.upper_normalizedSeparationDefectInt_nonneg, ?_,
    D.normalizedSeparationDefectInt_upper_eq_lower_add_residue,
    D.upper_normalizedSeparationDefectInt_lt_residue⟩
  rw [D.m_eq_oddTotal]
  exact F.upper_normalizedSeparationDefectInt_lt_oddTotal

/--
Farey interval `0 < D < G` まで含めた B first-failure normalized normal form。
-/
theorem bounded_normalized_crossing_strip
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
    let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
    qLower < 0 ∧
      0 ≤ qUpper ∧
      qUpper < (D.farey.m : ℤ) ∧
      qUpper = qLower + D.farey.residue ∧
      qUpper < D.farey.residue ∧
      0 < D.farey.residue ∧
      D.farey.residue < D.farey.G := by
  dsimp
  have hStrip := D.normalized_crossing_strip
  dsimp at hStrip
  refine ⟨hStrip.1, hStrip.2.1, hStrip.2.2.1,
    hStrip.2.2.2.1, hStrip.2.2.2.2,
    D.residue_pos, D.residue_lt_gap⟩

/--
旧 namespace からの互換 alias。
本体は `FirstFailureEdge.upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized`。
-/
theorem upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized
    {F : FirstFailureEdge} :
    (affineConst F.step.edge.upperWord : ℤ) =
      (wordTerminalGap F.step.edge.upperWord : ℤ) *
          (F.step.edge.upperR : ℤ) +
        (F.step.edge.modulus : ℤ) *
          normalizedSeparationDefectInt F.step.edge.upperWord :=
  F.upper_affineConst_eq_gap_mul_R_add_modulus_mul_normalized

end FirstFailureFareyData

/-! ## 4. canonical existence packets -/

namespace FirstFailureEdge

/-- canonical actual Farey packet を選べば normalized crossing strip は常に存在する。 -/
theorem exists_normalized_crossing_strip
    (F : FirstFailureEdge) :
    ∃ D : FirstFailureFareyData F,
      let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
      let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
      qLower < 0 ∧
        0 ≤ qUpper ∧
        qUpper < (D.farey.m : ℤ) ∧
        qUpper = qLower + D.farey.residue ∧
        qUpper < D.farey.residue := by
  let D := F.toFirstFailureFareyData
  exact ⟨D, D.normalized_crossing_strip⟩

/-- `0 < D < G` まで保持する canonical normalized crossing packet。 -/
theorem exists_bounded_normalized_crossing_strip
    (F : FirstFailureEdge) :
    ∃ D : FirstFailureFareyData F,
      let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
      let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
      qLower < 0 ∧
        0 ≤ qUpper ∧
        qUpper < (D.farey.m : ℤ) ∧
        qUpper = qLower + D.farey.residue ∧
        qUpper < D.farey.residue ∧
        0 < D.farey.residue ∧
        D.farey.residue < D.farey.G := by
  let D := F.toFirstFailureFareyData
  exact ⟨D, D.bounded_normalized_crossing_strip⟩

/-- polynomial-small residue error と normalized crossing strip を同時に保持する既存 packet。 -/
theorem exists_normalized_crossing_strip_with_polynomial_error
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    ∃ D : FirstFailureFareyData F,
      let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
      let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
      qLower < 0 ∧
        0 ≤ qUpper ∧
        qUpper < (D.farey.m : ℤ) ∧
        qUpper = qLower + D.farey.residue ∧
        qUpper < D.farey.residue ∧
        F.step.edge.upperR ≤
          K * (D.farey.k + 1) ^ (A + 1) := by
  let D := F.toFirstFailureFareyData
  have hStrip := D.normalized_crossing_strip
  dsimp at hStrip
  refine ⟨D, hStrip.1, hStrip.2.1, hStrip.2.2.1,
    hStrip.2.2.2.1, hStrip.2.2.2.2, ?_⟩
  exact D.upperR_le_lengthPolynomial hGap

/--
`0 < D < G`、normalized strip、polynomial-small upperR を同時に保持する B final packet。
-/
theorem exists_bounded_normalized_crossing_strip_with_polynomial_error
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    ∃ D : FirstFailureFareyData F,
      let qLower := normalizedSeparationDefectInt F.step.edge.lowerWord
      let qUpper := normalizedSeparationDefectInt F.step.edge.upperWord
      qLower < 0 ∧
        0 ≤ qUpper ∧
        qUpper < (D.farey.m : ℤ) ∧
        qUpper = qLower + D.farey.residue ∧
        qUpper < D.farey.residue ∧
        0 < D.farey.residue ∧
        D.farey.residue < D.farey.G ∧
        F.step.edge.upperR ≤
          K * (D.farey.k + 1) ^ (A + 1) := by
  let D := F.toFirstFailureFareyData
  have hStrip := D.bounded_normalized_crossing_strip
  dsimp at hStrip
  refine ⟨D, hStrip.1, hStrip.2.1, hStrip.2.2.1,
    hStrip.2.2.2.1, hStrip.2.2.2.2.1,
    hStrip.2.2.2.2.2.1, hStrip.2.2.2.2.2.2, ?_⟩
  exact D.upperR_le_lengthPolynomial hGap

end FirstFailureEdge

end CSTMicro
end Collatz2
