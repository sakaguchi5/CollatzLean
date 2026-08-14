import CollatzLean.Collatz2.Canonical.DualSigmaBudget

/-!
# Collatz2 Canonical: suffix/prefix budget difference

同じ word の二 budget

  K = p*2^H - 3B
  J = p*3^p - 3B

の差は whole center gap `G = 2^H - 3^p` の length 倍。

subtraction-free には exact に

  J + p*G = K

である。
-/

namespace Collatz2
namespace Word

/--
all-suffix-contracting + proper-prefix-positive word の budget difference。
-/
theorem budgetGapDifference
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hP : ProperPrefixesPositiveDeterminant w)
    (hne : w ≠ []) :
    prefixBudgetExcess w +
        oddSteps w * (AffineTransfer.ofWord w).centerGap =
      suffixBudgetExcess w := by
  have hSuffixLt :=
    hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow
      hne
  have hSuffixAdd :
      3 * affineConst w + suffixBudgetExcess w =
        oddSteps w * 2 ^ twoSteps w := by
    unfold suffixBudgetExcess
    omega
  have hPrefixAdd :=
    hP.three_mul_affineConst_add_prefixBudgetExcess
  have hC : Contracting w :=
    hAll.whole_contracting hne
  have hNeg :
      (AffineTransfer.ofWord w).determinant < 0 :=
    hC
  have hCoeffLe :
      (AffineTransfer.ofWord w).oddCoeff ≤
        (AffineTransfer.ofWord w).twoCoeff := by
    unfold AffineTransfer.determinant at hNeg
    omega
  have hGapCoeff :
      (AffineTransfer.ofWord w).centerGap +
          (AffineTransfer.ofWord w).oddCoeff =
        (AffineTransfer.ofWord w).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCoeffLe
  have hGap :
      (AffineTransfer.ofWord w).centerGap +
          3 ^ oddSteps w =
        2 ^ twoSteps w := by
    simpa using hGapCoeff
  have hGapScaled :=
    congrArg (fun z : ℕ => oddSteps w * z) hGap
  ring_nf at hSuffixAdd hPrefixAdd hGapScaled ⊢
  nlinarith

/-- FirstCrossing 版。 -/
theorem FirstCrossing.budgetGapDifference
    {w : Word}
    (hF : FirstCrossing w) :
    prefixBudgetExcess w +
        oddSteps w * (AffineTransfer.ofWord w).centerGap =
      suffixBudgetExcess w := by
  exact
    Word.budgetGapDifference
      hF.allSuffixesContracting
      hF.properPositive
      hF.nonempty

end Word
end Collatz2
