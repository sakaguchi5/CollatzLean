import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalFiniteXiIdentity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyConvergentCorridor

/-!
# Odd/even corrected finite-scan identities -> finite Xi bridge

`CriticalSturmianFiniteXiBridge` の一枚の field を、corrected formulas に沿って
odd/even の二つの finite `ZMod` identity に分解する。

ここが strong overlap と既存 `BoundaryXiTruncation` の finite scan formula を
実際に接続する場所である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalSturmianFiniteScanIdentity
    (D : CriticalContinuedFractionData)
    (O : CriticalSturmianStrongOverlap D) where
  odd_identity :
    ∀ j e m : ℕ,
      D.start ≤ j →
      j % 2 = 1 →
      e ≤ strongDenominatorWindowUpper D.q j →
      e = beattyIndex m →
      (criticalChristoffelPhiAt D j : ZMod (2 ^ e)) +
          criticalXiTruncationClass e m *
            (((3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j : ℤ) :
              ZMod (2 ^ e)) = 0

  even_identity :
    ∀ j e m : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      e ≤ strongDenominatorWindowUpper D.q j →
      e = beattyIndex m →
      (((2 : ℤ) ^ (D.q j - 1) -
          3 * criticalChristoffelPhiAt D j : ℤ) : ZMod (2 ^ e)) +
        criticalXiTruncationClass e m *
          ((3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) : ℤ) :
            ZMod (2 ^ e)) = 0

namespace CriticalSturmianFiniteScanIdentity

/-- branchwise finite scan identities assemble the existing Xi identity family. -/
theorem toCriticalFiniteXiIdentity
    {D : CriticalContinuedFractionData}
    {O : CriticalSturmianStrongOverlap D}
    (S : CriticalSturmianFiniteScanIdentity D O) :
    CriticalFiniteXiIdentity D := by
  refine ⟨?_⟩
  intro j e m hjStart hPrecision hem
  have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · unfold CriticalFiniteXiIdentityAt
    rw [correctedChristoffelP_odd D hjOdd]
    rw [correctedChristoffelQ_odd D hjOdd]
    exact S.odd_identity j e m hjStart hjOdd hPrecision hem
  · have hjEven : j % 2 = 0 := by omega
    unfold CriticalFiniteXiIdentityAt
    rw [correctedChristoffelP_even D hjEven]
    rw [correctedChristoffelQ_even D hjEven]
    exact S.even_identity j e m hjStart hjEven hPrecision hem

/-- branchwise scan proof gives the bridge object expected by the current pipeline. -/
theorem toCriticalSturmianFiniteXiBridge
    {D : CriticalContinuedFractionData}
    {O : CriticalSturmianStrongOverlap D}
    (S : CriticalSturmianFiniteScanIdentity D O) :
    CriticalSturmianFiniteXiBridge D O :=
  ⟨S.toCriticalFiniteXiIdentity⟩

end CriticalSturmianFiniteScanIdentity

end ExternalArithmetic
end CSTMicro
end Collatz2
