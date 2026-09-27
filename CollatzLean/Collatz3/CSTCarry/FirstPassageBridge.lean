import CollatzLean.Collatz3.CSTMicro.FirstPassageArithmetic
import CollatzLean.Collatz3.CSTCarry.MidpointDuality

/-!
# Collatz3 CSTCarry: first coefficient crossing と midpoint duality の bridge

既存 `CSTMicro.FirstPassagePath` は terminal length が
`criticalTwoDepth p = beattyIndex p + 1` と exact に一致する。
その結果、`p>0` では terminal coefficient `3^p / 2^H` は

  1/2 < 3^p / 2^H < 1

の strip に必ず入る。

この strip を `CSTCarry.MidpointDuality` に渡し、任意の H-bit shift `U` の binary MSB を
三進 quotient threshold `111...111_3` へ exact に移す。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

open CSTCarry

/-- positive odd count の first crossing では `3^p` は terminal 2 冪の上半分にある。 -/
theorem halfTwoPow_lt_threePow
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    2 ^ (P.length - 1) < 3 ^ P.endpointOddCount := by
  have hLen := P.length_eq_criticalTwoDepth
  have hLower := Critical.beattyIndex_lower_strict hp
  unfold Critical.criticalTwoDepth at hLen
  have hPred : P.length - 1 = Critical.beattyIndex P.endpointOddCount := by
    omega
  rw [hPred]
  exact hLower

/-- first crossing の terminal power strip。 -/
theorem terminalCoefficient_half_lt_one
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    2 ^ (P.length - 1) < 3 ^ P.endpointOddCount ∧
      3 ^ P.endpointOddCount < 2 ^ P.length := by
  exact ⟨P.halfTwoPow_lt_threePow hp, P.terminal_contracting⟩

/-- first-passage path に付随する ternary quotient。 -/
def ternaryShiftQuotient
    (P : FirstPassagePath)
    (U : ℕ) : ℕ :=
  (3 ^ P.endpointOddCount * U) / 2 ^ P.length

/--
任意の canonical H-bit shift `U` に対し、MSB 判定を三進 midpoint 比較へ移す。

右辺の `threeMidpoint p` は三進数で `111...111`（p 桁）。
-/
theorem shift_msb_iff_ternary_midpoint
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    {U : ℕ}
    (hU : U < 2 ^ P.length) :
    2 ^ (P.length - 1) ≤ U ↔
      CSTCarry.threeMidpoint P.endpointOddCount ≤ P.ternaryShiftQuotient U := by
  unfold ternaryShiftQuotient
  exact CSTCarry.power_midpoint_duality
    P.length_pos
    (P.halfTwoPow_lt_threePow hp)
    P.terminal_contracting
    hU

end FirstPassagePath
end CSTMicro
end Collatz3
