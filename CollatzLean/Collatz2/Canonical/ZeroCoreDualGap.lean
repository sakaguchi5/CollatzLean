import CollatzLean.Collatz2.Canonical.DualSigmaBudget
import CollatzLean.Collatz2.Canonical.ZeroCoreCanonicalSlacks
import CollatzLean.Collatz2.External.TwoThreeEffectiveGap

/-!
# Collatz2 Canonical: zero-core dual endpoint gap

true `j=0` zero core に対して、dual prefix budget を
canonical endpoint slack と effective 2-3 gap へ接続する。

主要結果:

  G*T < sigma*C

  2*G*C < sigma*C + G*(2*c+1)

effective linear gap の下で

  sigma < G
  T < C
  canonicalStart(v) < 2^K

まで得る。

ここで

  C = 3^length(v)
  G = centerGap(1::v)
  T = canonicalEnd(v)
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn
namespace CanonicalZeroCoreData

/-- whole odd-step slack `sigma = p - 6*n`。 -/
def sigma
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) : ℕ :=
  Word.oddSteps D.word - 6 * Z.natural.n

/-- `p = 6*n + sigma`。 -/
theorem oddSteps_eq_six_mul_n_add_sigma
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.oddSteps D.word =
      6 * Z.natural.n + Z.sigma := by
  obtain ⟨n, sigma0, _hn, _hsigma, hReturn, hp,
      _hSuffix, _hDual⟩ :=
    D.exists_dualSigmaBudget
  have hnEq :
      n = Z.natural.n := by
    have hNatural :=
      Z.natural.fullEnd_eq
    omega
  subst n
  unfold sigma
  rw [hp]
  omega

/-- sigma は正。 -/
theorem sigma_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    0 < Z.sigma := by
  obtain ⟨n, sigma0, _hn, hsigma0, hReturn, hp,
      _hSuffix, _hDual⟩ :=
    D.exists_dualSigmaBudget
  have hnEq :
      n = Z.natural.n := by
    have hNatural :=
      Z.natural.fullEnd_eq
    omega
  subst n
  have hSpec :=
    Z.oddSteps_eq_six_mul_n_add_sigma
  omega

--この2つのunusedは見直しが必要
/-- whole contracting gap `G` は正。 -/
theorem fullGap_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (_Z : CanonicalZeroCoreData D) :
    0 <
      (AffineTransfer.ofWord D.word).centerGap :=
  AffineTransfer.centerGap_pos_of_negative D.contracting

/-- whole gap は通常の `2^H - 3^p`。 -/
theorem fullGap_eq_twoPow_sub_threePow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (_Z : CanonicalZeroCoreData D) :
    (AffineTransfer.ofWord D.word).centerGap =
      2 ^ Word.twoSteps D.word -
        3 ^ Word.oddSteps D.word := by
  rfl

/-- tail length と whole length。 -/
theorem wholeOddSteps_eq_tailOddSteps_add_one
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    Word.oddSteps D.word =
      Word.oddSteps Z.natural.tail + 1 := by
  rw [Z.natural.word_eq]
  simp

/--
dual prefix budget の strict positivity から

  G*T < sigma*C

を得る。
-/
theorem dualEndpointGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D) :
    (AffineTransfer.ofWord D.word).centerGap *
        Word.canonicalEnd Z.natural.tail <
      Z.sigma *
        3 ^ Word.oddSteps Z.natural.tail := by
  obtain ⟨n, sigma0, _hn, _hsigma0, hReturn, hp,
      _hSuffix, hDual⟩ :=
    D.exists_dualSigmaBudget
  have hnEq :
      n = Z.natural.n := by
    have hNatural :=
      Z.natural.fullEnd_eq
    omega
  subst n
  have hSigmaEq :
      sigma0 = Z.sigma := by
    have hSpec :=
      Z.oddSteps_eq_six_mul_n_add_sigma
    omega
  rw [hSigmaEq] at hDual
  have hLen :=
    Z.wholeOddSteps_eq_tailOddSteps_add_one
  have hJpos :
      0 < Word.prefixBudgetExcess D.word :=
    D.firstCrossing.prefixBudgetExcess_pos
      D.word_length_gt_one
  have hDualTail :
      Z.sigma *
          (3 * 3 ^ Word.oddSteps Z.natural.tail) =
        3 *
            (AffineTransfer.ofWord D.word).centerGap *
            Word.canonicalEnd Z.natural.tail +
          Word.prefixBudgetExcess D.word := by
    rw [hLen, pow_succ, Z.fullEnd_eq_tailEnd] at hDual
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hDual
  nlinarith

/-- endpoint fundamental slack `c` の exact balance。 -/
theorem endpoint_add_one_add_two_mul_c_eq_two_mul_threePow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (L : Z.SlackData) :
    Word.canonicalEnd Z.natural.tail + 1 + 2 * L.c =
      2 * 3 ^ Word.oddSteps Z.natural.tail := by
  have hC :=
    L.threePow_eq
  have hT :=
    Z.natural.fullEnd_add_one
  rw [Z.fullEnd_eq_tailEnd] at hT
  nlinarith

/--
`dualEndpointGap` と endpoint slack を合わせた subtraction-free form:

  2*G*C < sigma*C + G*(2*c+1)
-/
theorem endpointSlackGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (L : Z.SlackData) :
    2 * (AffineTransfer.ofWord D.word).centerGap *
          3 ^ Word.oddSteps Z.natural.tail <
      Z.sigma * 3 ^ Word.oddSteps Z.natural.tail +
        (AffineTransfer.ofWord D.word).centerGap *
          (2 * L.c + 1) := by
  have hDual :=
    Z.dualEndpointGap
  have hSlack :=
    Z.endpoint_add_one_add_two_mul_c_eq_two_mul_threePow L
  have hG :=
    congrArg
      (fun x : ℕ =>
        (AffineTransfer.ofWord D.word).centerGap * x)
      hSlack
  ring_nf at hG ⊢
  nlinarith

/--
effective gap から whole pair の `19/12` linear gap。
-/
theorem nineteen_mul_oddSteps_lt_twelve_mul_fullGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    19 * Word.oddSteps D.word <
      12 * (AffineTransfer.ofWord D.word).centerGap := by
  have hpTwo :
      2 ≤ Word.oddSteps D.word := by
    have hlen :
        1 < Word.oddSteps D.word := by
      simpa [Word.oddSteps] using D.word_length_gt_one
    omega
  have hContract :
      3 ^ Word.oddSteps D.word <
        2 ^ Word.twoSteps D.word :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
  have h :=
    External.nineteen_mul_exponent_lt_twelve_mul_gap
      hEffective hpTwo hContract
  rw [Z.fullGap_eq_twoPow_sub_threePow]
  exact h

/--
`p = 6*n+sigma`, `n>0` と `19*p < 12*G` から

  sigma < G
-/
theorem sigma_lt_G_of_linearGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    Z.sigma <
      (AffineTransfer.ofWord D.word).centerGap := by
  have hSpec :=
    Z.oddSteps_eq_six_mul_n_add_sigma
  have hLinear :=
    Z.nineteen_mul_oddSteps_lt_twelve_mul_fullGap
      hEffective
  have hGpos :=
    Z.fullGap_pos
  have hn :=
    Z.natural.n_pos
  omega

/-- 今回直接使う `3*sigma < 2*G` 強化。 -/
theorem three_mul_sigma_lt_two_mul_G_of_linearGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    3 * Z.sigma <
      2 * (AffineTransfer.ofWord D.word).centerGap := by
  have hSpec :=
    Z.oddSteps_eq_six_mul_n_add_sigma
  have hLinear :=
    Z.nineteen_mul_oddSteps_lt_twelve_mul_fullGap
      hEffective
  have hn :=
    Z.natural.n_pos
  omega

/--
effective linear gap 下では canonical tail endpoint は fundamental interval の下半分:

  canonicalEnd(v) < 3^m
-/
theorem canonicalEnd_tail_lt_threePow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    Word.canonicalEnd Z.natural.tail <
      3 ^ Word.oddSteps Z.natural.tail := by
  have hDual :=
    Z.dualEndpointGap
  have hSigma :=
    Z.sigma_lt_G_of_linearGap hEffective
  have hCpos :
      0 < 3 ^ Word.oddSteps Z.natural.tail :=
    Nat.pow_pos (by omega)
  have hScaled :
      Z.sigma * 3 ^ Word.oddSteps Z.natural.tail <
        (AffineTransfer.ofWord D.word).centerGap *
          3 ^ Word.oddSteps Z.natural.tail :=
    (Nat.mul_lt_mul_right hCpos).2 hSigma
  have hChain :
      (AffineTransfer.ofWord D.word).centerGap *
          Word.canonicalEnd Z.natural.tail <
        (AffineTransfer.ofWord D.word).centerGap *
          3 ^ Word.oddSteps Z.natural.tail :=
    lt_trans hDual hScaled
  exact
    (Nat.mul_lt_mul_left Z.fullGap_pos).mp hChain

/--
effective linear gap 下では canonical tail start も fundamental interval の下半分:

  canonicalStart(v) < 2^K
-/
theorem canonicalStart_tail_lt_twoPow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (Z : CanonicalZeroCoreData D)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    Word.canonicalStart Z.natural.tail <
      2 ^ Word.twoSteps Z.natural.tail := by
  obtain ⟨n, sigma0, _hn, _hsigma0, hReturn, hp,
      hSuffix, _hDual⟩ :=
    D.exists_dualSigmaBudget
  have hnEq :
      n = Z.natural.n := by
    have hNatural :=
      Z.natural.fullEnd_eq
    omega
  subst n
  have hSigmaEq :
      sigma0 = Z.sigma := by
    have hSpec :=
      Z.oddSteps_eq_six_mul_n_add_sigma
    omega
  rw [hSigmaEq] at hSuffix
  have hKpos :=
    D.suffixBudgetExcess_pos
  have hBudget :
      3 * (AffineTransfer.ofWord D.word).centerGap *
            Word.canonicalStart D.word <
        Z.sigma * 2 ^ Word.twoSteps D.word := by
    nlinarith [hSuffix, hKpos]
  have hSigma :=
    Z.sigma_lt_G_of_linearGap hEffective
  have hPowPos :
      0 < 2 ^ Word.twoSteps D.word :=
    Nat.pow_pos (by omega)
  have hSigmaScaled :
      Z.sigma * 2 ^ Word.twoSteps D.word <
        (AffineTransfer.ofWord D.word).centerGap *
          2 ^ Word.twoSteps D.word :=
    (Nat.mul_lt_mul_right hPowPos).2 hSigma
  have hBeforeCancel :
      3 * (AffineTransfer.ofWord D.word).centerGap *
            Word.canonicalStart D.word <
        (AffineTransfer.ofWord D.word).centerGap *
          2 ^ Word.twoSteps D.word :=
    lt_trans hBudget hSigmaScaled
  have hPrefix :
      3 * Word.canonicalStart D.word <
        2 ^ Word.twoSteps D.word := by
    have hGpos :=
      Z.fullGap_pos
    have hScaled :
        (AffineTransfer.ofWord D.word).centerGap *
            (3 * Word.canonicalStart D.word) <
          (AffineTransfer.ofWord D.word).centerGap *
            2 ^ Word.twoSteps D.word := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        hBeforeCancel
    exact
      (Nat.mul_lt_mul_left hGpos).mp hScaled
  have hFullPow :
      2 ^ Word.twoSteps D.word =
        2 * 2 ^ Word.twoSteps Z.natural.tail := by
    rw [Z.natural.word_eq]
    simp [pow_add]
  have hPrefixTail :
      3 * Word.canonicalStart D.word <
        2 * 2 ^ Word.twoSteps Z.natural.tail := by
    rw [hFullPow] at hPrefix
    exact hPrefix
  have hHead :
      2 * Word.canonicalStart Z.natural.tail =
        3 * Word.canonicalStart D.word + 1 := by
    have hs :=
      Z.natural.boundary_add_one
    rw [Z.boundary_eq_tailStart] at hs
    have hS :=
      Z.natural.fullStart_add_one
    nlinarith
  have hLe :
      Word.canonicalStart Z.natural.tail ≤
        2 ^ Word.twoSteps Z.natural.tail := by
    omega
  have hTwoPos :
      0 < Word.twoSteps Z.natural.tail :=
    Word.twoSteps_pos_of_valid_nonempty
      Z.tail_valid Z.natural.tail_nonempty
  have hEven :
      Even (2 ^ Word.twoSteps Z.natural.tail) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hTwoPos)
  have hOdd :
      Odd (Word.canonicalStart Z.natural.tail) := by
    rw [← Z.boundary_eq_tailStart]
    rw [Z.natural.boundary_eq]
    exact O.value_odd (D.startIndex + 1)
  have hNe :
      Word.canonicalStart Z.natural.tail ≠
        2 ^ Word.twoSteps Z.natural.tail := by
    intro hEq
    rcases hOdd with ⟨a, ha⟩
    rcases hEven with ⟨b, hb⟩
    omega
  omega

end CanonicalZeroCoreData
end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
