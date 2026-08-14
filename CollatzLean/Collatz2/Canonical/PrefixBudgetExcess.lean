import CollatzLean.Collatz2.Local.TranslationDeterminant

/-!
# Collatz2 Canonical: proper-prefix budget excess

suffix 側の

  K = p * 2^H - 3B

に対する dual quantity として

  J = p * 3^p - 3B

を定義する。

FirstCrossing では proper-prefix determinant integral が非負なので

  3B + J = p * 3^p

が exact に成立する。
length > 1 なら `J > 0`。
-/

namespace Collatz2
namespace Word

/-- proper-prefix determinant budget の natural excess。 -/
def prefixBudgetExcess (w : Word) : ℕ :=
  oddSteps w * 3 ^ oddSteps w - 3 * affineConst w

/-- proper-prefix positive profile で exact addition form。 -/
theorem ProperPrefixesPositiveDeterminant.three_mul_affineConst_add_prefixBudgetExcess
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w) :
    3 * affineConst w + prefixBudgetExcess w =
      oddSteps w * 3 ^ oddSteps w := by
  have hle :=
    hP.three_mul_affineConst_le_oddSteps_mul_threePow
  unfold prefixBudgetExcess
  omega

/-- FirstCrossing 版。 -/
theorem FirstCrossing.three_mul_affineConst_add_prefixBudgetExcess
    {w : Word}
    (hF : FirstCrossing w) :
    3 * affineConst w + prefixBudgetExcess w =
      oddSteps w * 3 ^ oddSteps w :=
  hF.properPositive.three_mul_affineConst_add_prefixBudgetExcess

/-- length > 1 の FirstCrossing では prefix excess は正。 -/
theorem FirstCrossing.prefixBudgetExcess_pos
    {w : Word}
    (hF : FirstCrossing w)
    (hlen : 1 < w.length) :
    0 < prefixBudgetExcess w := by
  have hlt :=
    hF.three_mul_affineConst_lt_oddSteps_mul_threePow
      hlen
  unfold prefixBudgetExcess
  exact Nat.sub_pos_of_lt hlt

/--
`prefixBudgetExcess` は signed proper-prefix determinant integral の
natural shadow。

  (J : ℤ) = prefixDeterminantIntegral w
-/
theorem ProperPrefixesPositiveDeterminant.prefixBudgetExcess_int_eq_integral
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w) :
    (prefixBudgetExcess w : ℤ) =
      prefixDeterminantIntegral w := by
  have hadd :=
    hP.three_mul_affineConst_add_prefixBudgetExcess
  have hZ :
      (3 : ℤ) * (affineConst w : ℤ) +
          (prefixBudgetExcess w : ℤ) =
        (oddSteps w : ℤ) *
          ((3 : ℤ) ^ oddSteps w) := by
    exact_mod_cast hadd
  rw [prefixDeterminantIntegral_eq]
  linarith

/-- FirstCrossing 版。 -/
theorem FirstCrossing.prefixBudgetExcess_int_eq_integral
    {w : Word}
    (hF : FirstCrossing w) :
    (prefixBudgetExcess w : ℤ) =
      prefixDeterminantIntegral w :=
  hF.properPositive.prefixBudgetExcess_int_eq_integral

end Word
end Collatz2
