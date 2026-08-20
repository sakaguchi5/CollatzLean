import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalLastDepthParity

/-!
# Pure B: depth-two carry の mod-6 classification

`c-a >= 2` なら core は 9 で割れる。last depth `d=h(c-1)` は既に even なので
`d mod 6` は 0,2,4 のいずれか。

この checkpoint ではまずこの exact finite branching と、各 branch が次の column に
要求する 3-divisibility/nondivisibility を固定する。Beatty-gap 1/2 への完全 collapse は
次段の residue refinement で行う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- corridor depth が2以上なら last depth は mod 6 で 0/2/4 の三分岐。 -/
theorem depth_two_carry_modSix_classification
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (hTwo : 2 ≤ P.terminalCriticalStart - P.criticalizationStart) :
    let d := P.h (P.terminalCriticalStart - 1)
    d % 6 = 0 ∨ d % 6 = 2 ∨ d % 6 = 4 := by
  dsimp
  have hLt : P.criticalizationStart < P.terminalCriticalStart := by
    omega
  have hEven :=
    (P.criticalization_lt_terminal_iff_lastDepth_even hStart).1 hLt
  have hmod6 :
      P.h (P.terminalCriticalStart - 1) % 6 < 6 :=
    Nat.mod_lt _ (by decide)
  have hmod2 :
      (P.h (P.terminalCriticalStart - 1) % 6) % 2 = 0 := by
    omega
  omega

/-- depth-two corridor では core は 9 で割れる。 -/
theorem nine_dvd_terminalCore_of_depth_two
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (hTwo : 2 ≤ P.terminalCriticalStart - P.criticalizationStart) :
    (9 : ℤ) ∣ (P.terminalNoncriticalProfileCore : ℤ) := by
  have hExact := P.terminalCore_exactThreeAdicOrder hStart
  have hPow :
      (9 : ℤ) ∣
        (3 : ℤ) ^ (P.terminalCriticalStart - P.criticalizationStart) := by
    let r := P.terminalCriticalStart - P.criticalizationStart
    have hr : 2 ≤ r := by simpa [r] using hTwo
    refine ⟨(3 : ℤ) ^ (r - 2), ?_⟩
    have hExp : r = 2 + (r - 2) := by omega
    dsimp [r] at hExp ⊢
    rw [hExp, pow_add]
    norm_num
  exact hPow.trans hExact.1

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
