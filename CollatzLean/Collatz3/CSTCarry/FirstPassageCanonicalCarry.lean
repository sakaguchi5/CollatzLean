import CollatzLean.Collatz3.CSTCarry.FirstPassageRowBridge
import CollatzLean.Collatz3.CSTCarry.TernaryCorrection
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge

/-!
# Collatz3 CSTCarry: FirstPassagePath の canonical carry

`FirstPassageRowBridge` により path から canonical Ferrers rows が得られ、
`CarryDeterministic` によりその rows 上の ternary carry run は存在一意になった。

このファイルでは FirstPassagePath 自身に

* canonical ternary digits,
* canonical final carry,
* `CarryRealizes` realization,
* ternary correction 同定、
* `2 <= p <= 26` の final-wrap 排除、

を載せる。

これにより `P <= 26` の最終定理から外部 `CarryRealizes` witness 仮定を除去する。
-/

namespace Collatz3
namespace CSTMicro

open Critical

namespace FirstPassagePath

/-- FirstPassagePath 由来 rows の canonical ternary digit list。 -/
def canonicalTernaryDigits
    (P : FirstPassagePath) : List ℕ :=
  CSTCarry.canonicalCarryDigits
    (criticalTwoDepth P.endpointOddCount)
    P.carryRows
    0

/-- FirstPassagePath 由来 rows の canonical final carry。 -/
def canonicalCarryFinal
    (P : FirstPassagePath) : ℕ :=
  CSTCarry.canonicalFinalCarry
    (criticalTwoDepth P.endpointOddCount)
    P.carryRows
    0

/-- path 由来 canonical run は `CarryRealizes` を自動的に実現する。 -/
theorem canonicalCarry_realizes
    (P : FirstPassagePath) :
    CSTCarry.CarryRealizes
      (2 ^ criticalTwoDepth P.endpointOddCount)
      P.carryRows
      0
      P.canonicalTernaryDigits
      P.canonicalCarryFinal := by
  exact CSTCarry.canonicalCarryRun_realizes
    (criticalTwoDepth P.endpointOddCount) P.carryRows 0

/-- canonical digit 数は endpoint odd count と一致する。 -/
@[simp] theorem canonicalTernaryDigits_length
    (P : FirstPassagePath) :
    P.canonicalTernaryDigits.length = P.endpointOddCount := by
  have h := P.canonicalCarry_realizes.digits_length_eq
  simpa using h.trans P.carryRows_length

/--
FirstPassagePath の canonical ternary digit value は weighted defect から決まる
`-2^(-H)S mod 3^P` と exact に一致する。
-/
theorem canonicalTernaryDigits_value_eq_correction
    (P : FirstPassagePath) :
    CSTCarry.ternaryDigitsValue P.canonicalTernaryDigits =
      CSTCarry.ternaryCorrection
        (criticalTwoDepth P.endpointOddCount)
        P.carryRows.length
        (CSTCarry.ferrersWeightedDefect P.carryRows) := by
  exact P.canonicalCarry_realizes.ternaryDigitsValue_eq_ternaryCorrection

/-- row length を endpoint odd count に書き直した correction 同定。 -/
theorem canonicalTernaryDigits_value_eq_correction_endpoint
    (P : FirstPassagePath) :
    CSTCarry.ternaryDigitsValue P.canonicalTernaryDigits =
      CSTCarry.ternaryCorrection
        (criticalTwoDepth P.endpointOddCount)
        P.endpointOddCount
        (CSTCarry.ferrersWeightedDefect P.carryRows) := by
  simpa using P.canonicalTernaryDigits_value_eq_correction

/--
## witness-free P <= 26 final-wrap 排除

以前必要だった `CarryRealizes ... digits F` 仮定を canonical run の存在定理で除去する。
-/
theorem canonicalCarryFinal_lt_modulus_le_26
    (P : FirstPassagePath)
    (hp2 : 2 ≤ P.endpointOddCount)
    (hp26 : P.endpointOddCount ≤ 26) :
    P.canonicalCarryFinal <
      2 ^ criticalTwoDepth P.endpointOddCount := by
  exact P.final_lt_modulus_of_carryRows_le_26
    P.canonicalCarry_realizes hp2 hp26

/--
`P <= 26` では canonical final carry は binary shift の ordinary representative と一致する。
-/
theorem canonicalCarryFinal_eq_ferrersBinaryShift_le_26
    (P : FirstPassagePath)
    (hp2 : 2 ≤ P.endpointOddCount)
    (hp26 : P.endpointOddCount ≤ 26) :
    P.canonicalCarryFinal =
      CSTCarry.ferrersBinaryShift
        (criticalTwoDepth P.endpointOddCount) P.carryRows := by
  have hReal := P.canonicalCarry_realizes
  have hLt := P.canonicalCarryFinal_lt_modulus_le_26 hp2 hp26
  exact hReal.final_eq_ferrersBinaryShift_of_lt hLt

/--
FirstPassagePath 由来 rows に対する carry witness は canonical pair に存在一意。
-/
theorem existsUnique_canonicalCarry
    (P : FirstPassagePath) :
    ∃! out : List ℕ × ℕ,
      CSTCarry.CarryRealizes
        (2 ^ criticalTwoDepth P.endpointOddCount)
        P.carryRows
        0
        out.1
        out.2 := by
  exact CSTCarry.existsUnique_carryRealizes_twoPow
    (criticalTwoDepth P.endpointOddCount) P.carryRows 0

end FirstPassagePath
end CSTMicro
end Collatz3
