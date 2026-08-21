import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLeftSmallRoot
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CanonicalRepresentativeTrace
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBActualProfileCoordinateBridge

/-!
# Pure B single-corner: actual left critical-prefix bridge

single-corner の左側 `k < b` では depth が zero なので、actual odd-only checkpoint は
critical Beatty checkpoint と exact に一致する。

このファイルではまず一般の odd-only actual realization

  w : x -> y

から任意 odd-prefix `w.take k` の divisibility

  2^(twoSteps (w.take k)) |
    3^k x + affineConst (w.take k)

を取り出す。これを actual minimal B の upper exponent word に適用し、single-corner の
left rank `r=b-1` では prefix affine numerator が `criticalPrefixPhiZ r` に一致することから

  2^beta(r) | 3^r R_B + Psi(r)

を actual theorem として閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. odd-only whole realization -> prefix divisibility -/

/--
whole odd-only realization から任意 odd-prefix の 2-adic divisibility を取り出す。

suffix の odd coefficient `3^s` は `2^e` と coprime なので cancel できる。
-/
theorem wordPrefixDyadicDvdOfRealizes
    {w : Collatz2.Word}
    {x y k : ℕ}
    (hReal : Collatz2.Word.Realizes w x y)
    (hk : k ≤ Collatz2.Word.oddSteps w) :
    2 ^ Collatz2.Word.twoSteps (w.take k) ∣
      3 ^ k * x + Collatz2.Word.affineConst (w.take k) := by
  let u : Collatz2.Word := w.take k
  let v : Collatz2.Word := w.drop k
  have hkLen : k ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hk
  have huOdd : Collatz2.Word.oddSteps u = k := by
    dsimp [u, Collatz2.Word.oddSteps]
    exact List.length_take_of_le hkLen
  have hw : w = u ++ v := by
    dsimp [u, v]
    exact (List.take_append_drop k w).symm
  have hEq := (Collatz2.Word.realizes_iff w x y).1 hReal
  have hTwo :
      Collatz2.Word.twoSteps w =
        Collatz2.Word.twoSteps u + Collatz2.Word.twoSteps v := by
    rw [hw, Collatz2.Word.twoSteps_append]
  have hOdd :
      Collatz2.Word.oddSteps w =
        k + Collatz2.Word.oddSteps v := by
    rw [hw, Collatz2.Word.oddSteps_append, huOdd]
  have hAffine :
      Collatz2.Word.affineConst w =
        3 ^ Collatz2.Word.oddSteps v * Collatz2.Word.affineConst u +
          2 ^ Collatz2.Word.twoSteps u * Collatz2.Word.affineConst v := by
    rw [hw, Collatz2.Word.affineConst_append]
  rw [hTwo, hOdd, hAffine] at hEq
  simp only [pow_add] at hEq
  have hEqZ := congrArg (fun n : ℕ => (n : ℤ)) hEq
  push_cast at hEqZ
  have hRearr :
      (3 : ℤ) ^ k *
            (3 : ℤ) ^ Collatz2.Word.oddSteps v *
            (x : ℤ) +
          (3 : ℤ) ^ Collatz2.Word.oddSteps v *
            (Collatz2.Word.affineConst u : ℤ)
        =
      (2 : ℤ) ^ Collatz2.Word.twoSteps u *
            (2 : ℤ) ^ Collatz2.Word.twoSteps v *
            (y : ℤ) -
          (2 : ℤ) ^ Collatz2.Word.twoSteps u *
            (Collatz2.Word.affineConst v : ℤ) := by
    rw [hEqZ]
    ring
  have hScaled :
      (2 : ℤ) ^ Collatz2.Word.twoSteps u ∣
        (3 : ℤ) ^ Collatz2.Word.oddSteps v *
          ((3 : ℤ) ^ k * (x : ℤ) +
            (Collatz2.Word.affineConst u : ℤ)) := by
    refine ⟨
      (2 : ℤ) ^ Collatz2.Word.twoSteps v * (y : ℤ) -
        (Collatz2.Word.affineConst v : ℤ),
      ?_
    ⟩
    calc
      (3 : ℤ) ^ Collatz2.Word.oddSteps v *
          ((3 : ℤ) ^ k * (x : ℤ) +
            (Collatz2.Word.affineConst u : ℤ))
          =
        (3 : ℤ) ^ k *
              (3 : ℤ) ^ Collatz2.Word.oddSteps v *
              (x : ℤ) +
            (3 : ℤ) ^ Collatz2.Word.oddSteps v *
              (Collatz2.Word.affineConst u : ℤ) := by
                ring
      _ =
        (2 : ℤ) ^ Collatz2.Word.twoSteps u *
              (2 : ℤ) ^ Collatz2.Word.twoSteps v *
              (y : ℤ) -
            (2 : ℤ) ^ Collatz2.Word.twoSteps u *
              (Collatz2.Word.affineConst v : ℤ) := hRearr
      _ =
        (2 : ℤ) ^ Collatz2.Word.twoSteps u *
          ((2 : ℤ) ^ Collatz2.Word.twoSteps v * (y : ℤ) -
            (Collatz2.Word.affineConst v : ℤ)) := by
              ring
  have h23 : IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hcopLeft :
      IsCoprime
        ((2 : ℤ) ^ Collatz2.Word.twoSteps u)
        (3 : ℤ) :=
    h23.pow_left
  have hcop :
      IsCoprime
        ((2 : ℤ) ^ Collatz2.Word.twoSteps u)
        ((3 : ℤ) ^ Collatz2.Word.oddSteps v) :=
    hcopLeft.pow_right
  have hTargetZ :
      (2 : ℤ) ^ Collatz2.Word.twoSteps u ∣
        (3 : ℤ) ^ k * (x : ℤ) +
          (Collatz2.Word.affineConst u : ℤ) :=
    hcop.dvd_of_dvd_mul_left hScaled
  have hTargetNat :
      2 ^ Collatz2.Word.twoSteps u ∣
        3 ^ k * x + Collatz2.Word.affineConst u := by
    exact_mod_cast hTargetZ
  simpa [u] using hTargetNat

/-- realization が与える canonical odd-prefix state。 -/
noncomputable def realizedPrefixState
    {w : Collatz2.Word}
    {x y : ℕ}
    (hReal : Collatz2.Word.Realizes w x y)
    (k : ℕ)
    (hk : k ≤ Collatz2.Word.oddSteps w) : ℕ :=
  Classical.choose (wordPrefixDyadicDvdOfRealizes hReal hk)

/-- canonical odd-prefix state の exact specification。 -/
theorem realizedPrefixState_spec
    {w : Collatz2.Word}
    {x y : ℕ}
    (hReal : Collatz2.Word.Realizes w x y)
    (k : ℕ)
    (hk : k ≤ Collatz2.Word.oddSteps w) :
    3 ^ k * x + Collatz2.Word.affineConst (w.take k) =
      2 ^ Collatz2.Word.twoSteps (w.take k) *
        realizedPrefixState hReal k hk := by
  exact Classical.choose_spec (wordPrefixDyadicDvdOfRealizes hReal hk)

/-! ## 2. actual first-failure upper word wrappers -/

namespace FirstFailureEdge

/-- first-failure upper exponent word は canonical `R -> R+q` を actual に実現する。 -/
theorem upperExponentWord_realizesCanonical
    (F : FirstFailureEdge) :
    Collatz2.Word.Realizes F.upperExponentWord
      F.step.edge.upperR
      (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
  rw [Collatz2.Word.realizes_iff]
  have hA :=
    F.upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
  have hContract := F.upperExponentWord_firstCrossing.terminalContracting
  have hPow :
      3 ^ Collatz2.Word.oddSteps F.upperExponentWord <
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1 hContract
  have hGap :
      Collatz2.Word.terminalGap F.upperExponentWord +
          3 ^ Collatz2.Word.oddSteps F.upperExponentWord =
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord := by
    unfold Collatz2.Word.terminalGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  calc
    2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
        (F.step.edge.upperR + F.upperNormalizedDefectNat)
        =
      (Collatz2.Word.terminalGap F.upperExponentWord +
          3 ^ Collatz2.Word.oddSteps F.upperExponentWord) *
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
          rw [hGap]
    _ =
      3 ^ Collatz2.Word.oddSteps F.upperExponentWord * F.step.edge.upperR +
        (Collatz2.Word.terminalGap F.upperExponentWord * F.step.edge.upperR +
          2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
            F.upperNormalizedDefectNat) := by
          rw [← hGap]
          ring
    _ =
      3 ^ Collatz2.Word.oddSteps F.upperExponentWord * F.step.edge.upperR +
        Collatz2.Word.affineConst F.upperExponentWord := by
          rw [← hA]

end FirstFailureEdge

namespace MinimalActualABObstructionPacket

/-- actual first-failure upper parity word は minimal bad word 自身。 -/
theorem actualFirstFailureUpperWord_eq_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
  unfold ActualABObstructionPacket.firstFailureEdge
  unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
  unfold FirstFailureProvenance.toFirstFailureEdge
  dsimp
  exact M.failureStep_upperWord_eq_word

/-- actual upper exponent word は minimal bad word の run encoding。 -/
theorem actualUpperExponentWord_eq_exponentWordOfParity
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.firstFailureEdge.upperExponentWord =
      exponentWordOfParity M.word := by
  unfold FirstFailureEdge.upperExponentWord
  rw [M.actualFirstFailureUpperWord_eq_word]

/-- actual upper exponent word の odd depth は pure profile の `m`。 -/
theorem actualUpperExponentWord_oddSteps_eq_profile_m
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    Collatz2.Word.oddSteps M.actual.firstFailureEdge.upperExponentWord =
      (M.toPureBProfileObstruction hL).m := by
  rw [M.actualUpperExponentWord_eq_exponentWordOfParity]
  rw [oddSteps_exponentWordOfParity]
  exact (M.toPureBProfileObstruction_m_eq_wordOddCount hL).symm

/-- proper odd cut では actual upper prefix depth と pure profile checkpoint が一致。 -/
theorem actualUpperPrefixTwoDepth_eq_profileCheckpoint
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k < (M.toPureBProfileObstruction hL).m) :
    Collatz2.Word.prefixTwoDepth
        M.actual.firstFailureEdge.upperExponentWord k =
      profileCheckpoint (M.toPureBProfileObstruction hL).h k := by
  let P := M.toPureBProfileObstruction hL
  have hCoord :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL
      (Nat.le_of_lt hk)
  rw [P.profileEndpointCheckpoint_of_lt hk] at hCoord
  rw [M.actualUpperExponentWord_eq_exponentWordOfParity]
  exact hCoord.symm

/--
single-corner の左 critical prefix divisibility は actual geometry から自動的に従う。

これは後段で `SingleCornerLargeMEliminationCertificate.leftPrefixDivisibility` を
そのまま埋められる raw actual theorem。
-/
theorem singleCorner_leftPrefixDivisibility
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    (2 : ℤ) ^ beattyIndex (S.b - 1) ∣
      (3 : ℤ) ^ (S.b - 1) *
          (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        criticalPrefixPhiZ (S.b - 1) := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let r := S.b - 1
  have hmW : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hrLtB : r < S.b := by
    dsimp [r]
    exact S.leftRank_lt_b
  have hbM : S.b < P.m :=
    lt_of_lt_of_le S.b_lt_c P.terminalCriticalStart_spec.1
  have hrLeW : r ≤ Collatz2.Word.oddSteps w := by
    rw [hmW]
    omega
  have hActualCheckpoint :
      ∀ k : ℕ, k < S.b →
        Collatz2.Word.prefixTwoDepth w k = beattyIndex k := by
    intro k hkb
    have hkM : k < P.m := lt_trans hkb hbM
    have hCoord := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hkM
    have hLeft := S.left_checkpoint_eq_beatty hkb
    simpa [w, F, P] using hCoord.trans hLeft
  have hReal :
      Collatz2.Word.Realizes w
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [w] using FirstFailureEdge.upperExponentWord_realizesCanonical F
  have hDivNat :=
    wordPrefixDyadicDvdOfRealizes
      (w := w)
      (x := F.step.edge.upperR)
      (y := F.step.edge.upperR + F.upperNormalizedDefectNat)
      hReal hrLeW
  have hrLen : r ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hrLeW
  have hProfileAffine :
      profileAffineNumerator r (fun _ => 0) =
        Collatz2.Word.affineConst (w.take r) := by
    apply profileAffineNumerator_eq_affineConst_of_checkpoint
    · simp [Collatz2.Word.oddSteps, List.length_take_of_le hrLen]
    · intro k hk
      have hkr : k < r := hk
      have hkb : k < S.b := lt_trans hkr hrLtB
      have hTake :
          Collatz2.Word.prefixTwoDepth (w.take r) k =
            Collatz2.Word.prefixTwoDepth w k := by
        unfold Collatz2.Word.prefixTwoDepth
        rw [List.take_take]
        rw [min_eq_left (Nat.le_of_lt hkr)]
      unfold profileCheckpoint
      simp only [Nat.sub_zero]
      rw [hTake, hActualCheckpoint k hkb]
  have hZeroProfile :
      profileAffineNumerator r (fun _ => 0) = criticalPrefixPhiNat r := by
    unfold profileAffineNumerator criticalPrefixPhiNat profileCheckpoint
    simp
  have hAffineCritical :
      Collatz2.Word.affineConst (w.take r) = criticalPrefixPhiNat r :=
    hProfileAffine.symm.trans hZeroProfile
  have hDepthR :
      Collatz2.Word.twoSteps (w.take r) = beattyIndex r := by
    change Collatz2.Word.prefixTwoDepth w r = beattyIndex r
    exact hActualCheckpoint r hrLtB
  rw [hDepthR, hAffineCritical] at hDivNat
  have hDivZ :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (F.step.edge.upperR : ℤ) +
          (criticalPrefixPhiNat r : ℤ) := by
    exact_mod_cast hDivNat
  rw [criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ] at hDivZ
  simpa [r, F] using hDivZ

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
