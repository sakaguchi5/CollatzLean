import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalInitialSquareBand
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianSquareWindow14

/-!
# Construct the degree-14 Sturmian square window from BHZ + Rhin

ここで初めて

* BHZ/Ostrowski: 一つの P-band 内で square root を見つける
* Rhin: adjacent convergent の gap を degree 14 で抑える

を合成する。

BHZ port 自身には exponent 14 は含まれていない。
したがってこの construction が、既存 abstract interface
`CriticalSturmianSquareWindow14` の実際の source decomposition になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- low-index finite band と Rhin tail を同時に吸収する absolute coefficient。 -/
def criticalSquareWindowGrowthConstant
    (B : BHZCriticalInitialSquareBand) : ℕ :=
  B.bandConstant * max (criticalPowerP 9) 32768

/-- 上の coefficient は positive。 -/
theorem criticalSquareWindowGrowthConstant_pos
    (B : BHZCriticalInitialSquareBand) :
    0 < criticalSquareWindowGrowthConstant B := by
  unfold criticalSquareWindowGrowthConstant
  have hMax : 0 < max (criticalPowerP 9) 32768 := by
    exact lt_of_lt_of_le (by norm_num : 0 < 32768)
      (le_max_right _ _)
  exact Nat.mul_pos B.bandConstant_pos hMax

/--
BHZ band theorem と Rhin degree-14 growth から、
phase-uniform `CriticalSturmianSquareWindow14` を canonical に構成する。
-/
noncomputable def criticalSturmianSquareWindow14FromBHZ
    (B : BHZCriticalInitialSquareBand)
    (R : RhinLinearForm14) :
    CriticalSturmianSquareWindow14 := {
  constant := criticalSquareWindowGrowthConstant B
  constant_pos := criticalSquareWindowGrowthConstant_pos B
  exists_square := by
    intro s N hN
    obtain ⟨j, hjTwo, hLower, hUpper⟩ :=
      exists_criticalPowerP_band hN
    rcases
        B.exists_square_in_band
          s N j hjTwo hLower hUpper with
      ⟨r, hNr, hrBand, hSquare⟩
    refine ⟨r, hNr, ?_, hSquare⟩
    by_cases hjNine : 9 ≤ j
    · have hPNext :=
        R.criticalPowerP_next_le_32768_mul_pow14 hjNine
      have hPjPow :
          criticalPowerP j ^ 14 ≤ (N + 1) ^ 14 := by
        apply Nat.pow_le_pow_left
        omega
      have hK :
          32768 ≤ max (criticalPowerP 9) 32768 :=
        le_max_right _ _
      calc
        r
            ≤ B.bandConstant * criticalPowerP (j + 1) := hrBand
        _ ≤ B.bandConstant *
              (32768 * criticalPowerP j ^ 14) :=
            Nat.mul_le_mul_left B.bandConstant hPNext
        _ =
            (B.bandConstant * 32768) *
              criticalPowerP j ^ 14 := by ring
        _ ≤
            (B.bandConstant * max (criticalPowerP 9) 32768) *
              (N + 1) ^ 14 := by
            exact Nat.mul_le_mul
              (Nat.mul_le_mul_left B.bandConstant hK)
              hPjPow
        _ =
            criticalSquareWindowGrowthConstant B *
              (N + 1) ^ 14 := by
            rfl
    · have hjLt : j < 9 := by omega
      have hIndexLe : j + 1 ≤ 9 := by omega
      have hPFinite :
          criticalPowerP (j + 1) ≤ criticalPowerP 9 := by
        exact
          criticalPowerP_mono_from_two
            (by omega)
            hIndexLe
      have hPMax :
          criticalPowerP 9 ≤ max (criticalPowerP 9) 32768 :=
        le_max_left _ _
      have hPowOne : 1 ≤ (N + 1) ^ 14 := by
        positivity
      calc
        r
            ≤ B.bandConstant * criticalPowerP (j + 1) := hrBand
        _ ≤ B.bandConstant * criticalPowerP 9 :=
            Nat.mul_le_mul_left B.bandConstant hPFinite
        _ ≤ B.bandConstant * max (criticalPowerP 9) 32768 :=
            Nat.mul_le_mul_left B.bandConstant hPMax
        _ =
            criticalSquareWindowGrowthConstant B * 1 := by
            simp [criticalSquareWindowGrowthConstant]
        _ ≤
            criticalSquareWindowGrowthConstant B *
              (N + 1) ^ 14 :=
            Nat.mul_le_mul_left
              (criticalSquareWindowGrowthConstant B)
              hPowOne
}

/-- constructor の constant projection。 -/
@[simp] theorem criticalSturmianSquareWindow14FromBHZ_constant
    (B : BHZCriticalInitialSquareBand)
    (R : RhinLinearForm14) :
    (criticalSturmianSquareWindow14FromBHZ B R).constant =
      criticalSquareWindowGrowthConstant B := by
  rfl

/-- construction の exists-square theorem を直接使う thin wrapper。 -/
theorem exists_criticalSquare_degree14_from_BHZ
    (B : BHZCriticalInitialSquareBand)
    (R : RhinLinearForm14)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      N ≤ r ∧
      r ≤ criticalSquareWindowGrowthConstant B * (N + 1) ^ 14 ∧
      CriticalBeattySquareAt s r := by
  exact
    (criticalSturmianSquareWindow14FromBHZ B R).exists_square
      s N hN

end ExternalArithmetic
end CSTMicro
end Collatz2
