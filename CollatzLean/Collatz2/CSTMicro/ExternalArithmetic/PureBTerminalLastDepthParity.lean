import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreRightCarryChain

/-!
# Pure B: arithmetic/geometric criticalization と last depth parity

terminal core の mod-3 digit は last noncritical column だけで決まる。
その column mass は

  2^(β-h) (2^h-1)

なので 3-divisibility は `h` の偶奇そのもの。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `3 | 2^n-1` は `n` 偶数と exact 同値。 -/
theorem three_dvd_twoPow_sub_one_iff_mod_two_eq_zero
    (n : ℕ) :
    (3 : ℤ) ∣ ((2 : ℤ) ^ n - 1) ↔ n % 2 = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      by_cases hn1 : n = 1
      · subst n
        norm_num
      let k := n - 2
      have hk : k < n := by
        dsimp [k]
        omega
      have hn : n = k + 2 := by
        dsimp [k]
        omega
      have hmod : n % 2 = k % 2 := by
        omega
      have hpow :
          (2 : ℤ) ^ n - 1 =
            ((2 : ℤ) ^ k - 1) +
              3 * (2 : ℤ) ^ k := by
        rw [hn, pow_add]
        norm_num
        ring
      rw [hpow, hmod]
      have hsmall := ih k hk
      constructor
      · intro hsum
        apply hsmall.1
        rcases hsum with ⟨t, ht⟩
        refine ⟨t - (2 : ℤ) ^ k, ?_⟩
        linear_combination ht
      · intro heven
        have hsmallDvd :
            (3 : ℤ) ∣ (2 : ℤ) ^ k - 1 :=
          hsmall.2 heven
        rcases hsmallDvd with ⟨t, ht⟩
        refine ⟨t + (2 : ℤ) ^ k, ?_⟩
        linear_combination ht

/-- admissible column mass の 3-divisibility は depth parity。 -/
theorem three_dvd_rightmostColumnMass_iff_depth_even
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {k : ℕ}
    (hk : k < m) :
    (3 : ℤ) ∣ (profileRightmostColumnMass h k : ℤ) ↔
      h k % 2 = 0 := by
  have hDepth := A.depth_le hk
  have hExp :
      beattyIndex k = (beattyIndex k - h k) + h k := by
    omega
  have hPowLe :
      2 ^ (beattyIndex k - h k) ≤ 2 ^ beattyIndex k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  have hFactor :
      (profileRightmostColumnMass h k : ℤ) =
        (2 : ℤ) ^ (beattyIndex k - h k) *
          ((2 : ℤ) ^ (h k) - 1) := by
    unfold profileRightmostColumnMass
    rw [Nat.cast_sub hPowLe]
    push_cast
    rw [hExp, pow_add]
    have hCancel :
        beattyIndex k - h k + h k - h k =
          beattyIndex k - h k := by
      omega
    rw [hCancel]
    ring
  rw [hFactor]
  constructor
  · intro hDvd
    have hTail :
        (3 : ℤ) ∣ ((2 : ℤ) ^ (h k) - 1) := by
      have hCoprime :=
        PureBProfileObstruction.threePow_isCoprime_twoPow 1 (beattyIndex k - h k)
      simpa using hCoprime.dvd_of_dvd_mul_left hDvd
    exact (three_dvd_twoPow_sub_one_iff_mod_two_eq_zero (h k)).1 hTail
  · intro hEven
    have hTail :=
      (three_dvd_twoPow_sub_one_iff_mod_two_eq_zero (h k)).2 hEven
    exact dvd_mul_of_dvd_right hTail _

namespace PureBProfileObstruction

/-- terminal critical start が正なら、その直前は genuine noncritical column。 -/
theorem terminalLastDepth_pos
    (P : PureBProfileObstruction)
    (hcPos : 0 < P.terminalCriticalStart) :
    0 < P.h (P.terminalCriticalStart - 1) := by
  let c := P.terminalCriticalStart
  have Sc : IsTerminalCriticalSuffix P c := by
    simpa [c] using P.terminalCriticalStart_spec
  have hcLe : c ≤ P.m := Sc.1
  by_contra hnot
  have hnot' :
      ¬ 0 < P.h (c - 1) := by
    simpa [c] using hnot
  have hzero :
      P.h (c - 1) = 0 :=
    Nat.eq_zero_of_not_pos hnot'
  have Sprev : IsTerminalCriticalSuffix P (c - 1) := by
    constructor
    · omega
    · intro k hk hkm
      by_cases hEq : k = c - 1
      · subst k
        exact hzero
      · have hck : c ≤ k := by omega
        exact Sc.2 k hck hkm
  have hMin := P.terminalCriticalStart_minimal Sprev
  dsimp [c] at hMin hcPos
  omega

/-- terminal core の 3-divisibility は last noncritical depth の偶奇。 -/
theorem three_dvd_terminalCore_iff_lastDepth_even
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ∣ (P.terminalNoncriticalProfileCore : ℤ) ↔
      P.h (P.terminalCriticalStart - 1) % 2 = 0 := by
  have hcPos : 0 < P.terminalCriticalStart := by
    have hle := P.criticalizationStart_le_terminalCriticalStart
    omega
  have hDecomp := P.terminalCore_rightCarryDecomposition hcPos
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hDecomp
  push_cast at hCast
  have hThreePrefix :
      (3 : ℤ) ∣
        3 * (profileDyadicClosedNumerator
          (P.terminalCriticalStart - 1) P.h : ℤ) := by
    exact ⟨_, rfl⟩
  have hIffMass :
      ((3 : ℤ) ∣ (P.terminalNoncriticalProfileCore : ℤ)) ↔
        ((3 : ℤ) ∣ (P.terminalLastColumnMass : ℤ)) := by
    constructor
    · intro hCore
      rw [hCast] at hCore
      have hSub := dvd_sub hCore hThreePrefix
      simpa using hSub
    · intro hMass
      rw [hCast]
      exact dvd_add hMass hThreePrefix
  rw [hIffMass]
  unfold terminalLastColumnMass
  apply three_dvd_rightmostColumnMass_iff_depth_even P.admissible
  have hcLe := P.terminalCriticalStart_spec.1
  omega

/-- arithmetic/geometric criticalization が一致する iff last depth は odd。 -/
theorem criticalization_eq_terminal_iff_lastDepth_odd
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    P.criticalizationStart = P.terminalCriticalStart ↔
      P.h (P.terminalCriticalStart - 1) % 2 = 1 := by
  have hcPos : 0 < P.terminalCriticalStart := by
    have hle := P.criticalizationStart_le_terminalCriticalStart
    omega
  have hPos := P.terminalLastDepth_pos hcPos
  have hEven := P.three_dvd_terminalCore_iff_lastDepth_even hStart
  have hUnit :=
    P.not_three_dvd_terminalCore_iff_criticalization_eq_terminalCriticalStart hStart
  have hmod : P.h (P.terminalCriticalStart - 1) % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  constructor
  · intro hEq
    have hNotThree := hUnit.2 hEq
    have hNotEven :
        ¬ P.h (P.terminalCriticalStart - 1) % 2 = 0 := by
      intro hz
      exact hNotThree (hEven.2 hz)
    omega
  · intro hOdd
    apply hUnit.1
    intro hThree
    have h0 := hEven.1 hThree
    omega

/-- positive corridor iff last depth は even。 -/
theorem criticalization_lt_terminal_iff_lastDepth_even
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    P.criticalizationStart < P.terminalCriticalStart ↔
      P.h (P.terminalCriticalStart - 1) % 2 = 0 := by
  rw [← P.three_dvd_terminalCore_iff_lastDepth_even hStart]
  exact
    (P.three_dvd_terminalCore_iff_criticalization_lt_terminalCriticalStart hStart).symm

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
