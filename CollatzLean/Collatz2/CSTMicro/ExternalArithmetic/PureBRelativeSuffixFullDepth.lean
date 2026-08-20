import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBShiftedDefectStateIdentities

/-!
# Pure B relative bridge 1: full-depth の suffix 伝播

interval defect の concat law

  F[a,b](y)
    = 3^(b-c) F[a,c](y)
      + 2^(β(c)-β(a)) F[c,b](y)

から、whole interval が full 3-adic depth `b-a` を持てば、任意 suffix `[c,b)` も
その長さ `b-c` だけ full-depth を持つことを取り出す。

後段では arithmetic criticalization window `[a,m)` の deep divisibility を canonical
block boundary へ輸送するために使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
whole interval の full 3-adic depth は任意 suffix へ伝播する。
-/
theorem criticalIntervalDefectZ_suffix_fullDepth
    {a c b : ℕ}
    {y : ℤ}
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (hDeep :
      (3 : ℤ) ^ (b - a) ∣
        criticalIntervalDefectZ a b y) :
    (3 : ℤ) ^ (b - c) ∣
      criticalIntervalDefectZ c b y := by
  have hExp : b - a = (b - c) + (c - a) := by
    omega
  have hWhole :
      (3 : ℤ) ^ (b - c) ∣
        criticalIntervalDefectZ a b y := by
    rcases hDeep with ⟨z, hz⟩
    refine ⟨(3 : ℤ) ^ (c - a) * z, ?_⟩
    rw [hz, hExp, pow_add]
    ring
  have hHead :
      (3 : ℤ) ^ (b - c) ∣
        (3 : ℤ) ^ (b - c) *
          criticalIntervalDefectZ a c y := by
    exact ⟨criticalIntervalDefectZ a c y, rfl⟩
  have hConcat :=
    criticalIntervalDefectZ_concat hac hcb y
  have hScaled :
      (3 : ℤ) ^ (b - c) ∣
        (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
          criticalIntervalDefectZ c b y := by
    have hDiff := dvd_sub hWhole hHead
    have hEq :
        criticalIntervalDefectZ a b y -
            (3 : ℤ) ^ (b - c) *
              criticalIntervalDefectZ a c y =
          (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
            criticalIntervalDefectZ c b y := by
      linarith
    rw [hEq] at hDiff
    exact hDiff
  exact
    (PureBProfileObstruction.threePow_isCoprime_twoPow
      (b - c) (beattyIndex c - beattyIndex a)).dvd_of_dvd_mul_left hScaled

end ExternalArithmetic
end CSTMicro
end Collatz2
