import CollatzLean.Collatz2.Canonical.PrefixBudgetExcess
import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn

/-!
# Collatz2 Canonical: dual sigma budget

canonical-positive FirstCrossing には suffix / prefix の二つの exact budget がある。

half-gap `n`、length slack `sigma`、whole center gap `G`、
start/end を `S,T` とすると

  sigma * 2^H = 3 * G * S + K
  sigma * 3^p = 3 * G * T + J

ここで

  K = suffixBudgetExcess
  J = prefixBudgetExcess

である。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
suffix / prefix の dual sigma budget を同じ `n,sigma` で回収する。
-/
theorem exists_dualSigmaBudget
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    ∃ n sigma : ℕ,
      0 < n ∧
      0 < sigma ∧
      Word.canonicalEnd D.word =
        Word.canonicalStart D.word + 2 * n ∧
      Word.oddSteps D.word = 6 * n + sigma ∧
      sigma * 2 ^ Word.twoSteps D.word =
        3 * (AffineTransfer.ofWord D.word).centerGap *
              Word.canonicalStart D.word +
          Word.suffixBudgetExcess D.word ∧
      sigma * 3 ^ Word.oddSteps D.word =
        3 * (AffineTransfer.ofWord D.word).centerGap *
              Word.canonicalEnd D.word +
          Word.prefixBudgetExcess D.word := by
  obtain ⟨n, sigma, hn, hsigma, hreturn, hp, hSuffix⟩ :=
    D.exists_halfGap_sigma_budgetIdentity
  have hAll := D.allSuffixesContracting
  obtain ⟨n', hn', hreturn', hAffine⟩ :=
    hAll.exists_canonicalHalfGap_and_exactBalance
      D.word_valid D.word_nonempty D.canonicalPositive
  have hnEq : n' = n := by
    omega
  subst n'
  have hPrefix :=
    D.firstCrossing.three_mul_affineConst_add_prefixBudgetExcess
  have hPrefix' :
      3 * Word.affineConst D.word +
          Word.prefixBudgetExcess D.word =
        Word.oddSteps D.word *
          3 ^ Word.oddSteps D.word := by
    simpa [word] using hPrefix
  have hNeg :
      (AffineTransfer.ofWord D.word).determinant < 0 :=
    D.contracting
  have hCoeffLe :
      (AffineTransfer.ofWord D.word).oddCoeff ≤
        (AffineTransfer.ofWord D.word).twoCoeff := by
    unfold AffineTransfer.determinant at hNeg
    omega
  have hGapCoeff :
      (AffineTransfer.ofWord D.word).centerGap +
          (AffineTransfer.ofWord D.word).oddCoeff =
        (AffineTransfer.ofWord D.word).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCoeffLe
  have hGap :
      (AffineTransfer.ofWord D.word).centerGap +
          3 ^ Word.oddSteps D.word =
        2 ^ Word.twoSteps D.word := by
    simpa using hGapCoeff
  have hDual :
      sigma * 3 ^ Word.oddSteps D.word =
        3 * (AffineTransfer.ofWord D.word).centerGap *
              Word.canonicalEnd D.word +
          Word.prefixBudgetExcess D.word := by
    have hPrefix0 := hPrefix'
    rw [hAffine, pow_succ] at hPrefix0
    have hPrefixLinear :
        3 *
              ((AffineTransfer.ofWord D.word).centerGap *
                  Word.canonicalStart D.word +
                2 ^ Word.twoSteps D.word * 2 * n) +
            Word.prefixBudgetExcess D.word =
          (6 * n + sigma) *
            3 ^ Word.oddSteps D.word := by
      calc
        3 *
              ((AffineTransfer.ofWord D.word).centerGap *
                  Word.canonicalStart D.word +
                2 ^ Word.twoSteps D.word * 2 * n) +
            Word.prefixBudgetExcess D.word
            =
          Word.oddSteps D.word *
            3 ^ Word.oddSteps D.word := hPrefix0
        _ =
          (6 * n + sigma) *
            3 ^ Word.oddSteps D.word := by
          rw [hp]
    rw [hreturn]
    have hGapScaled :=
      congrArg
        (fun z : ℕ => 6 * n * z)
        hGap
    ring_nf at hPrefixLinear hGapScaled ⊢
    nlinarith
  exact
    ⟨n, sigma, hn, hsigma, hreturn, hp,
      hSuffix, hDual⟩

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
