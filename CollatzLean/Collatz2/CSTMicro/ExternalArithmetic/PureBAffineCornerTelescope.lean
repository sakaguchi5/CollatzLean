import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerTerminalCore

/-!
# Pure B: affine corner telescope

extended checkpoints `p_0,...,p_m` と run gaps `e_k=p_(k+1)-p_k` に対し

  B_k = 2^p_k * 3^(m-k-1),
  alpha_k = 2^e_k - 2

と置く。

exact telescope

  A(h) + G = sum_{k<m} alpha_k B_k

を証明する。`e_k=1` なら `alpha_k=0` なので、global affine quantity は
run gap `>=2` の corners のみに support を持つ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

namespace PureBProfileObstruction

/-- corner coefficient `2^e_k-2`。 -/
noncomputable def profileCornerCoefficient
    (P : PureBProfileObstruction)
    (k : ℕ) : ℕ :=
  2 ^ P.profileRunGap k - 2

/-- affine monomial `B_k`。 -/
noncomputable def profileCornerMonomial
    (P : PureBProfileObstruction)
    (k : ℕ) : ℕ :=
  2 ^ P.profileEndpointCheckpoint k *
    3 ^ (P.m - (k + 1))

/-- corner-supported affine mass。 -/
noncomputable def profileCornerMass
    (P : PureBProfileObstruction) : ℕ :=
  Finset.sum (Finset.range P.m)
    (fun k => P.profileCornerCoefficient k * P.profileCornerMonomial k)

/-- telescope 用の shifted term `Q_k = 2^p_k 3^(m-k)`。 -/
noncomputable def profileEndpointScaledTermZ
    (P : PureBProfileObstruction)
    (k : ℕ) : ℤ :=
  (2 : ℤ) ^ P.profileEndpointCheckpoint k *
    (3 : ℤ) ^ (P.m - k)

/-- extended checkpoints は全 adjacent positions で strict。 -/
theorem profileEndpointCheckpoint_strict_succ
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    P.profileEndpointCheckpoint k <
      P.profileEndpointCheckpoint (k + 1) := by
  by_cases hk1 : k + 1 < P.m
  · rw [P.profileEndpointCheckpoint_of_lt hk]
    rw [P.profileEndpointCheckpoint_of_lt hk1]
    exact P.admissible.checkpoint_strict hk1
  · have hkEnd : k + 1 = P.m := by omega
    rw [hkEnd, P.profileEndpointCheckpoint_m]
    rw [P.profileEndpointCheckpoint_of_lt hk]
    have hCheckpointLe : profileCheckpoint P.h k ≤ beattyIndex k := by
      unfold profileCheckpoint
      omega
    have hBeatty : beattyIndex k < beattyIndex P.m :=
      beattyIndex_strictMono hk
    rw [P.terminal_beatty]
    omega

/-- every actual run gap is positive。 -/
theorem profileRunGap_pos
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    0 < P.profileRunGap k := by
  unfold profileRunGap
  exact Nat.sub_pos_of_lt (P.profileEndpointCheckpoint_strict_succ hk)

/-- run gap `1` の coefficient は zero。 -/
theorem profileCornerCoefficient_eq_zero_of_runGap_eq_one
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hGap : P.profileRunGap k = 1) :
    P.profileCornerCoefficient k = 0 := by
  simp [profileCornerCoefficient, hGap]

/-- proper index では corner monomial は ordinary profile affine term。 -/
theorem profileCornerMonomial_eq_affineTerm
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    P.profileCornerMonomial k =
      2 ^ profileCheckpoint P.h k * 3 ^ (P.m - (k + 1)) := by
  simp [profileCornerMonomial, P.profileEndpointCheckpoint_of_lt hk]

/-- all corner monomials の plain sum は profile affine numerator。 -/
theorem sum_profileCornerMonomial_eq_profileAffineNumerator
    (P : PureBProfileObstruction) :
    Finset.sum (Finset.range P.m) P.profileCornerMonomial =
      profileAffineNumerator P.m P.h := by
  unfold profileAffineNumerator
  apply Finset.sum_congr rfl
  intro k hkMem
  exact P.profileCornerMonomial_eq_affineTerm (Finset.mem_range.mp hkMem)

/-- finite shifted-sum identity。 -/
theorem sum_range_succ_shift_add_zero
    (f : ℕ → ℤ)
    (m : ℕ) :
    Finset.sum (Finset.range m) (fun k => f (k + 1)) + f 0 =
      Finset.sum (Finset.range m) f + f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        (Finset.sum (Finset.range m) (fun k => f (k + 1)) +
            f (m + 1)) + f 0
            =
          (Finset.sum (Finset.range m) (fun k => f (k + 1)) +
            f 0) + f (m + 1) := by
              ring
        _ =
          (Finset.sum (Finset.range m) f + f m) +
            f (m + 1) := by
              rw [ih]

/-- `Q_k = 3 B_k` for proper cuts。 -/
theorem profileEndpointScaledTermZ_eq_three_mul_monomial
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    P.profileEndpointScaledTermZ k =
      3 * (P.profileCornerMonomial k : ℤ) := by
  unfold profileEndpointScaledTermZ profileCornerMonomial
  have hExp : P.m - k = (P.m - (k + 1)) + 1 := by omega
  rw [hExp, pow_succ]
  push_cast
  ring

/-- `Q_0 = 3^m`。 -/
theorem profileEndpointScaledTermZ_zero
    (P : PureBProfileObstruction) :
    P.profileEndpointScaledTermZ 0 = (3 : ℤ) ^ P.m := by
  have h0M : 0 < P.m :=
    lt_trans Nat.zero_lt_one P.one_lt_m
  have hDepth0 := P.admissible.depth_le h0M
  have hH0 : P.h 0 = 0 := by
    rw [beattyIndex_zero] at hDepth0
    omega
  unfold profileEndpointScaledTermZ
  rw [P.profileEndpointCheckpoint_of_lt h0M]
  unfold profileCheckpoint
  rw [hH0, beattyIndex_zero]
  simp

/-- `Q_m = 2^H`。 -/
theorem profileEndpointScaledTermZ_m
    (P : PureBProfileObstruction) :
    P.profileEndpointScaledTermZ P.m = (2 : ℤ) ^ P.H := by
  unfold profileEndpointScaledTermZ
  rw [P.profileEndpointCheckpoint_m]
  simp

/-- one corner term の local exact difference。 -/
theorem profileCornerTerm_cast_eq_endpointDifference
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    ((P.profileCornerCoefficient k * P.profileCornerMonomial k : ℕ) : ℤ) =
      P.profileEndpointScaledTermZ (k + 1) -
        2 * (P.profileCornerMonomial k : ℤ) := by
  have hStrict := P.profileEndpointCheckpoint_strict_succ hk
  have hGapPos := P.profileRunGap_pos hk
  have hGapEq :
      P.profileEndpointCheckpoint (k + 1) =
        P.profileEndpointCheckpoint k + P.profileRunGap k := by
    unfold profileRunGap
    omega
  have hTwoLe : 2 ≤ 2 ^ P.profileRunGap k := by
    have hOne : 1 ≤ P.profileRunGap k := by omega
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ P.profileRunGap k :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hOne
  unfold profileCornerCoefficient profileCornerMonomial profileEndpointScaledTermZ
  rw [Nat.cast_mul, Nat.cast_sub hTwoLe]
  push_cast
  rw [hGapEq, pow_add]
  ring

/-- profile gap の signed form `G = 2^H-3^m`。 -/
theorem gap_cast_eq_twoPow_sub_threePow_endpoint
    (P : PureBProfileObstruction) :
    (P.gap : ℤ) = (2 : ℤ) ^ P.H - (3 : ℤ) ^ P.m := by
  have hGapNat : 3 ^ P.m < 2 ^ P.H := by
    have hPos : 0 < 2 ^ P.H - 3 ^ P.m := by
      simpa [PureBProfileObstruction.gap, columnLayerGap] using P.gap_pos
    exact Nat.sub_pos_iff_lt.mp hPos
  unfold PureBProfileObstruction.gap columnLayerGap
  rw [Nat.cast_sub (Nat.le_of_lt hGapNat)]
  push_cast
  rfl

/--
main affine corner telescope, signed form。
-/
theorem profileCornerMass_cast_eq_affine_add_gap
    (P : PureBProfileObstruction) :
    (P.profileCornerMass : ℤ) =
      (profileAffineNumerator P.m P.h : ℤ) + (P.gap : ℤ) := by
  let Q : ℕ → ℤ := P.profileEndpointScaledTermZ
  have hShift := sum_range_succ_shift_add_zero Q P.m
  have hQSum :
      Finset.sum (Finset.range P.m) Q =
        3 * (profileAffineNumerator P.m P.h : ℤ) := by
    calc
      Finset.sum (Finset.range P.m) Q
          = Finset.sum (Finset.range P.m)
              (fun k => 3 * (P.profileCornerMonomial k : ℤ)) := by
              apply Finset.sum_congr rfl
              intro k hkMem
              exact P.profileEndpointScaledTermZ_eq_three_mul_monomial
                (Finset.mem_range.mp hkMem)
      _ = 3 *
          Finset.sum (Finset.range P.m)
            (fun k => (P.profileCornerMonomial k : ℤ)) := by
              rw [Finset.mul_sum]
      _ = 3 * (profileAffineNumerator P.m P.h : ℤ) := by
              have hNat :=
                P.sum_profileCornerMonomial_eq_profileAffineNumerator
              have hCast :=
                congrArg
                  (fun n : ℕ => (n : ℤ))
                  hNat
              push_cast at hCast
              rw [hCast]
  have hQ0 := P.profileEndpointScaledTermZ_zero
  have hQm := P.profileEndpointScaledTermZ_m
  have hShiftSolved :
      Finset.sum (Finset.range P.m) (fun k => Q (k + 1)) =
        3 * (profileAffineNumerator P.m P.h : ℤ) +
          (2 : ℤ) ^ P.H - (3 : ℤ) ^ P.m := by
    dsimp [Q] at hShift
    rw [hQSum, hQ0, hQm] at hShift
    linarith
  unfold profileCornerMass
  push_cast
  calc
    Finset.sum (Finset.range P.m)
        (fun k =>
          ((P.profileCornerCoefficient k : ℕ) : ℤ) *
            ((P.profileCornerMonomial k : ℕ) : ℤ))
        =
      Finset.sum (Finset.range P.m)
        (fun k =>
          Q (k + 1) - 2 * (P.profileCornerMonomial k : ℤ)) := by
            apply Finset.sum_congr rfl
            intro k hkMem
            simpa [Q] using
              P.profileCornerTerm_cast_eq_endpointDifference
                (Finset.mem_range.mp hkMem)
    _ =
      Finset.sum (Finset.range P.m) (fun k => Q (k + 1)) -
        2 * Finset.sum (Finset.range P.m)
          (fun k => (P.profileCornerMonomial k : ℤ)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ =
      (profileAffineNumerator P.m P.h : ℤ) +
        ((2 : ℤ) ^ P.H - (3 : ℤ) ^ P.m) := by
            rw [hShiftSolved]
            have hNat := P.sum_profileCornerMonomial_eq_profileAffineNumerator
            have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
            push_cast at hCast
            rw [hCast]
            ring
    _ =
      (profileAffineNumerator P.m P.h : ℤ) + (P.gap : ℤ) := by
            rw [P.gap_cast_eq_twoPow_sub_threePow_endpoint]

/-- natural-number form of the same exact telescope。 -/
theorem profileCornerMass_eq_affine_add_gap
    (P : PureBProfileObstruction) :
    P.profileCornerMass = profileAffineNumerator P.m P.h + P.gap := by
  exact_mod_cast P.profileCornerMass_cast_eq_affine_add_gap

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
