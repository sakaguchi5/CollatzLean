import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape
import CollatzLean.Collatz3.Bridge.SurvivorDefectNormalizedActual

/-!
# Collatz3 CSTConditional: A 型 normalized escape bound から actual compact state へ

`LinearDefectLowerBound` の下では既存 theorem により `R_m` は一様有界で実数極限を持つ。
`V_m < R_m/2` と合わせるだけで、actual defect-normalized value

`V_m = value(m) / 2^(δ_m+2)`

も同じ tail 全体で一様有界になる。

新しい A 型 predicate は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
linear defect survivor では defect-normalized actual state が explicit に一様有界。

`V_m < (R_(K*N) + 2K/3)/2`。
-/
theorem defectNormalizedActualValue_lt_uniform_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (m : ℕ) :
    O.defectNormalizedActualValue m <
      (O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3) / 2 := by
  have hV := O.defectNormalizedActualValue_lt_escape_div_two SInf m
  have hR := O.normalizedEscapeCoordinate_le_uniform_of_linearDefect
    SInf hLinear m
  linarith

/-- linear defect survivor の defect-normalized actual state の range は上に有界。 -/
theorem defectNormalizedActualValue_bddAbove_of_linearDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    BddAbove (Set.range O.defectNormalizedActualValue) := by
  refine ⟨(O.normalizedEscapeCoordinate (K * N) + 2 * (K : ℝ) / 3) / 2, ?_⟩
  rintro y ⟨m, rfl⟩
  exact (O.defectNormalizedActualValue_lt_uniform_of_linearDefect
    SInf hLinear m).le

end OddOrbit
end Collatz3
