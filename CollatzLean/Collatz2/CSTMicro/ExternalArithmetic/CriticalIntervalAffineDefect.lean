import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

/-!
# Critical interval affine defect calculus

`CriticalPrefixOstrowski` で arbitrary shifted interval `[a,b)` は origin-prefix の差へ
移された。このファイルでは、その interval 自身に numerator / power-gap / affine defect
を持たせ、cut `a ≤ c ≤ b` に関して三者が同じ positive-linear law を満たすことを示す。

  Φ[a,b]
    = 3^(b-c) Φ[a,c]
      + 2^(β_c-β_a) Φ[c,b]

  Γ[a,b]
    = 3^(b-c) Γ[a,c]
      + 2^(β_c-β_a) Γ[c,b]

  F[a,b](y)
    = 3^(b-c) F[a,c](y)
      + 2^(β_c-β_a) F[c,b](y)

ここで

  Γ[a,b] = 2^(β_b-β_a) - 3^(b-a)
  F[a,b](y) = Φ[a,b] - Γ[a,b] y.

これは既存 `ChristoffelWronskian` の numerator / gap transport と同型の algebra であり、
Stage 5 では profile の深い global cancellation を block defect へ輸送するために使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- shifted critical interval の signed power gap。 -/
def criticalIntervalGapZ
    (a b : ℕ) : ℤ :=
  (2 : ℤ) ^ (beattyIndex b - beattyIndex a) -
    (3 : ℤ) ^ (b - a)

/-- shifted critical interval の affine defect。 -/
def criticalIntervalDefectZ
    (a b : ℕ)
    (y : ℤ) : ℤ :=
  criticalIntervalPhiZ a b -
    criticalIntervalGapZ a b * y

/-- origin-prefix の signed power gap。 -/
def criticalPrefixGapZ
    (n : ℕ) : ℤ :=
  (2 : ℤ) ^ beattyIndex n -
    (3 : ℤ) ^ n

/-- origin-prefix の affine defect。 -/
def criticalPrefixDefectZ
    (n : ℕ)
    (y : ℤ) : ℤ :=
  criticalPrefixPhiZ n -
    criticalPrefixGapZ n * y

/-- このファイル内で使う Beatty index の weak monotonicity。 -/
private theorem beattyIndex_mono_of_le_interval
    {a b : ℕ}
    (hab : a ≤ b) :
    beattyIndex a ≤ beattyIndex b := by
  by_cases hEq : a = b
  · subst b
    exact le_rfl
  · exact le_of_lt (beattyIndex_strictMono (by omega))

/-- origin-prefix gap も interval gap と同じ endpoint decomposition を持つ。 -/
theorem criticalPrefixGapZ_endpoint_decomposition
    {a b : ℕ}
    (hab : a ≤ b) :
    criticalPrefixGapZ b =
      (3 : ℤ) ^ (b - a) * criticalPrefixGapZ a +
        (2 : ℤ) ^ beattyIndex a * criticalIntervalGapZ a b := by
  have hBeta : beattyIndex a ≤ beattyIndex b :=
    beattyIndex_mono_of_le_interval hab
  have hBetaExp :
      beattyIndex b =
        beattyIndex a + (beattyIndex b - beattyIndex a) := by
    omega
  have hThreeExp :
      b = (b - a) + a := by
    omega
  have hTwo :
      (2 : ℤ) ^ beattyIndex b =
        (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^ (beattyIndex b - beattyIndex a) := by
    calc
      (2 : ℤ) ^ beattyIndex b
          =
        (2 : ℤ) ^
          (beattyIndex a + (beattyIndex b - beattyIndex a)) := by
            rw [hBetaExp]
            simp
      _ =
        (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^ (beattyIndex b - beattyIndex a) := by
            rw [pow_add]
  have hThree :
      (3 : ℤ) ^ b =
        (3 : ℤ) ^ (b - a) * (3 : ℤ) ^ a := by
    calc
      (3 : ℤ) ^ b
          =
        (3 : ℤ) ^ ((b - a) + a) := by
            rw [hThreeExp]
            simp
      _ =
        (3 : ℤ) ^ (b - a) * (3 : ℤ) ^ a := by
            rw [pow_add]
  unfold criticalPrefixGapZ criticalIntervalGapZ
  rw [hTwo, hThree]
  ring


/-- origin-prefix defect の exact endpoint decomposition。 -/
theorem criticalPrefixDefectZ_endpoint_decomposition
    {a b : ℕ}
    (hab : a ≤ b)
    (y : ℤ) :
    criticalPrefixDefectZ b y =
      (3 : ℤ) ^ (b - a) * criticalPrefixDefectZ a y +
        (2 : ℤ) ^ beattyIndex a * criticalIntervalDefectZ a b y := by
  have hPhi := criticalPrefixPhiZ_endpoint_decomposition hab
  have hGap := criticalPrefixGapZ_endpoint_decomposition hab
  unfold criticalPrefixDefectZ criticalIntervalDefectZ
  rw [hPhi, hGap]
  ring

/-- interval numerator の cut law。 -/
theorem criticalIntervalPhiZ_concat
    {a c b : ℕ}
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    criticalIntervalPhiZ a b =
      (3 : ℤ) ^ (b - c) * criticalIntervalPhiZ a c +
        (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
          criticalIntervalPhiZ c b := by
  have hab : a ≤ b := le_trans hac hcb
  have hAB := criticalPrefixPhiZ_endpoint_decomposition hab
  have hAC := criticalPrefixPhiZ_endpoint_decomposition hac
  have hCB := criticalPrefixPhiZ_endpoint_decomposition hcb
  have hBeta : beattyIndex a ≤ beattyIndex c :=
    beattyIndex_mono_of_le_interval hac
  have hBetaExp :
      beattyIndex c =
        beattyIndex a + (beattyIndex c - beattyIndex a) := by
    omega
  have hThreeExp :
      b - a = (b - c) + (c - a) := by
    omega
  have hTwoPow :
      (2 : ℤ) ^ beattyIndex c =
        (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^ (beattyIndex c - beattyIndex a) := by
    rw [hBetaExp, pow_add]
    simp
  have hThreePow :
      (3 : ℤ) ^ (b - a) =
        (3 : ℤ) ^ (b - c) *
          (3 : ℤ) ^ (c - a) := by
    rw [hThreeExp, pow_add]
  have hScaled :
      (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a b =
        (2 : ℤ) ^ beattyIndex a *
          ((3 : ℤ) ^ (b - c) * criticalIntervalPhiZ a c +
            (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
              criticalIntervalPhiZ c b) := by
    calc
      (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a b
          = criticalPrefixPhiZ b -
              (3 : ℤ) ^ (b - a) * criticalPrefixPhiZ a := by
              linarith
      _ =
          (2 : ℤ) ^ beattyIndex a *
            ((3 : ℤ) ^ (b - c) * criticalIntervalPhiZ a c +
              (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
                criticalIntervalPhiZ c b) := by
            rw [hCB, hAC, hTwoPow, hThreePow]
            ring
  have hTwoNe :
      (2 : ℤ) ^ beattyIndex a ≠ 0 :=
    pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  exact mul_left_cancel₀ hTwoNe hScaled

/-- interval gap の cut law。 -/
theorem criticalIntervalGapZ_concat
    {a c b : ℕ}
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    criticalIntervalGapZ a b =
      (3 : ℤ) ^ (b - c) * criticalIntervalGapZ a c +
        (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
          criticalIntervalGapZ c b := by
  have hBetaAC : beattyIndex a ≤ beattyIndex c :=
    beattyIndex_mono_of_le_interval hac
  have hBetaCB : beattyIndex c ≤ beattyIndex b :=
    beattyIndex_mono_of_le_interval hcb
  have hBetaExp :
      beattyIndex b - beattyIndex a =
        (beattyIndex c - beattyIndex a) +
          (beattyIndex b - beattyIndex c) := by
    omega
  have hThreeExp :
      b - a = (b - c) + (c - a) := by
    omega
  unfold criticalIntervalGapZ
  rw [hBetaExp, hThreeExp, pow_add, pow_add]
  ring

/-- interval affine defect の cut law。 -/
theorem criticalIntervalDefectZ_concat
    {a c b : ℕ}
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (y : ℤ) :
    criticalIntervalDefectZ a b y =
      (3 : ℤ) ^ (b - c) * criticalIntervalDefectZ a c y +
        (2 : ℤ) ^ (beattyIndex c - beattyIndex a) *
          criticalIntervalDefectZ c b y := by
  have hPhi := criticalIntervalPhiZ_concat hac hcb
  have hGap := criticalIntervalGapZ_concat hac hcb
  unfold criticalIntervalDefectZ
  rw [hPhi, hGap]
  ring

/-- empty interval の numerator は zero。 -/
@[simp] theorem criticalIntervalPhiZ_self
    (a : ℕ) :
    criticalIntervalPhiZ a a = 0 := by
  simp [criticalIntervalPhiZ]

/-- empty interval の gap は zero。 -/
@[simp] theorem criticalIntervalGapZ_self
    (a : ℕ) :
    criticalIntervalGapZ a a = 0 := by
  simp [criticalIntervalGapZ]

/-- empty interval の defect は zero。 -/
@[simp] theorem criticalIntervalDefectZ_self
    (a : ℕ)
    (y : ℤ) :
    criticalIntervalDefectZ a a y = 0 := by
  simp [criticalIntervalDefectZ]

/-- origin-prefix numerator は origin interval numerator と一致する。 -/
theorem criticalPrefixPhiZ_eq_interval_zero
    (n : ℕ) :
    criticalPrefixPhiZ n = criticalIntervalPhiZ 0 n := by
  have h :=
    criticalPrefixPhiZ_endpoint_decomposition
      (a := 0) (b := n) (by omega : 0 ≤ n)
  simp only [criticalPrefixPhiZ, criticalIntervalPhiZ, Nat.Ico_zero_eq_range,
             beattyIndex_zero, tsub_zero]


/-- origin-prefix gap は origin interval gap と一致する。 -/
theorem criticalPrefixGapZ_eq_interval_zero
    (n : ℕ) :
    criticalPrefixGapZ n = criticalIntervalGapZ 0 n := by
  unfold criticalPrefixGapZ criticalIntervalGapZ
  simp

/-- origin-prefix defect は origin interval defect と一致する。 -/
theorem criticalPrefixDefectZ_eq_interval_zero
    (n : ℕ)
    (y : ℤ) :
    criticalPrefixDefectZ n y = criticalIntervalDefectZ 0 n y := by
  unfold criticalPrefixDefectZ criticalIntervalDefectZ
  rw [criticalPrefixPhiZ_eq_interval_zero]
  rw [criticalPrefixGapZ_eq_interval_zero]

end ExternalArithmetic
end CSTMicro
end Collatz2
