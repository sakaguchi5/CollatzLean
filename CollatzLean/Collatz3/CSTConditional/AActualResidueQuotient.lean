import CollatzLean.Collatz3.CSTConditional.ADefectNormalizedActual
import CollatzLean.Collatz3.Bridge.SurvivorDefectActualResidue

/-!
# Collatz3 CSTConditional: A 型 actual residue と ordinary quotient の一様有限化

`a_m = value(m) mod 2^(δ_m+2)` と
`k_m = value(m) / 2^(δ_m+2)` により

`value(m) = a_m + 2^(δ_m+2) k_m`

である。

既存 A 型 bound は compact state

`V_m < (R_(K*N) + 2K/3)/2`

を一様に抑える。`k_m ≤ V_m` なので ordinary quotient `k_m` も
同じ実数 bound の下に一様に入る。

一方 `a_m` は有限 future word の canonical start から exact に決まる。
従って late A 型 actual value は

`有限 future residue + 一様 bounded ordinary lift`

という形へ落ちる。

新しい state は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/-- linear defect survivor では ordinary quotient も explicit に一様有界。 -/
theorem defectActualQuotient_lt_uniform_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (m : ℕ) :
    (O.defectActualQuotient m : ℝ) <
      (O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3) / 2 := by
  have hQ := O.defectActualQuotient_le_defectNormalizedActualValue m
  have hV := O.defectNormalizedActualValue_lt_uniform_of_linearDefect
    SInf hLinear m
  exact lt_of_le_of_lt hQ hV

/--
A 型 actual value の finite-residue / bounded-lift package。

residue は有限 future word だけで決まり、ordinary quotient は `m` に依らない
同じ explicit real bound の下に入る。
-/
theorem actualValue_finiteFutureResidue_boundedLift_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (m : ℕ) :
    O.value m =
        (Word.canonicalStart
            (O.segmentWord m (infiniteSurvivorDefect O.exponent m + 2)) %
          2 ^ (infiniteSurvivorDefect O.exponent m + 2)) +
        2 ^ (infiniteSurvivorDefect O.exponent m + 2) *
          O.defectActualQuotient m ∧
      (O.defectActualQuotient m : ℝ) <
        (O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3) / 2 := by
  exact
    ⟨O.value_eq_futureCanonicalResidue_add_modulus_mul_quotient m,
      O.defectActualQuotient_lt_uniform_of_linearDefect SInf hLinear m⟩

end OddOrbit
end Collatz3
