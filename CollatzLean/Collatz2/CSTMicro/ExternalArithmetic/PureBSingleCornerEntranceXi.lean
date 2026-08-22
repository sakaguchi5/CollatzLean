import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerActualLeftPrefix

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: entrance Xi bridge

single-corner の入口 `b` では

* `k < b` では extra depth が 0、
* `h b = 1`

なので、`b` odd steps までの affine numerator はまだ critical numerator `Psi_b`
そのものだが、prefix two-depth は `beta_b - 1` へ一段だけ下がる。

従って actual upper representative `R_B` は

  2^(beta_b - 1) | 3^b R_B + Psi_b

を満たす。

さらに arbitrary precision `e` について

  Xi_e(m) = - Psi_m * 3^(-m)  in ZMod(2^e)

を有限 recurrence から証明する。これにより入口 divisibility は exact に

  R_B = Xi_(beta_b-1)(b)

という residue equality へ変換される。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. critical prefix numerator と finite Xi の arbitrary-precision identity -/

/-- critical prefix numerator の one-step recurrence。 -/
theorem criticalPrefixPhiZ_succ_entranceXi
    (n : ℕ) :
    criticalPrefixPhiZ (n + 1) =
      3 * criticalPrefixPhiZ n +
        (2 : ℤ) ^ beattyIndex n := by
  classical
  unfold criticalPrefixPhiZ
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range n)
          (fun k =>
            (2 : ℤ) ^ beattyIndex k *
              (3 : ℤ) ^ (n + 1 - 1 - k)) =
        3 *
          Finset.sum (Finset.range n)
            (fun k =>
              (2 : ℤ) ^ beattyIndex k *
                (3 : ℤ) ^ (n - 1 - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < n := Finset.mem_range.mp hk
    have hExp :
        n + 1 - 1 - k = (n - 1 - k) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLast : n + 1 - 1 - n = 0 := by omega
  rw [hLast, pow_zero, mul_one]

/--
`Psi_m` は任意 precision `e` で
`3^m * beattyInverseContribution e m` の numerator になっている。
-/
theorem criticalPrefixPhiZ_cast_eq_threePow_mul_beattyInverseContribution
    (e m : ℕ) :
    ((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) =
      (3 : ZMod (2 ^ e)) ^ m *
        beattyInverseContribution e m := by
  induction m with
  | zero =>
      simp [criticalPrefixPhiZ]
  | succ m ih =>
      rw [criticalPrefixPhiZ_succ_entranceXi]
      push_cast
      rw [beattyInverseContribution_succ, mul_add]
      have hTerm :
          (3 : ZMod (2 ^ e)) ^ (m + 1) *
              ((2 : ZMod (2 ^ e)) ^ beattyIndex m *
                invThreePow e (m + 1)) =
            (2 : ZMod (2 ^ e)) ^ beattyIndex m := by
        have hInv := threePow_mul_invThreePow e (m + 1)
        calc
          (3 : ZMod (2 ^ e)) ^ (m + 1) *
                ((2 : ZMod (2 ^ e)) ^ beattyIndex m *
                  invThreePow e (m + 1))
              =
            (2 : ZMod (2 ^ e)) ^ beattyIndex m *
              ((3 : ZMod (2 ^ e)) ^ (m + 1) *
                invThreePow e (m + 1)) := by
                  ring
          _ = (2 : ZMod (2 ^ e)) ^ beattyIndex m := by
                rw [hInv]
                ring
      rw [hTerm, ih, pow_succ]
      ring

/--
finite Xi truncation class は arbitrary precision で
`-Psi_m * 3^(-m)` に exact に一致する。
-/
theorem criticalXiTruncationClass_eq_neg_phi_mul_invThreePow
    (e m : ℕ) :
    criticalXiTruncationClass e m =
      -(((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) *
        invThreePow e m) := by
  unfold criticalXiTruncationClass
  rw [criticalPrefixPhiZ_cast_eq_threePow_mul_beattyInverseContribution]
  have hInv := threePow_mul_invThreePow e m
  calc
    - beattyInverseContribution e m
        = -(beattyInverseContribution e m * 1) := by ring
    _ =
        -(beattyInverseContribution e m *
          ((3 : ZMod (2 ^ e)) ^ m * invThreePow e m)) := by
            rw [hInv]
    _ =
        -(((3 : ZMod (2 ^ e)) ^ m *
              beattyInverseContribution e m) *
            invThreePow e m) := by
              ring

/--
任意 precision `e` で

  2^e | 3^m x + Psi_m

なら、`x` の class は finite critical Xi truncation class そのもの。
`e = beattyIndex m` を要求しないことが入口 port の要点。
-/
theorem natCast_eq_criticalXi_of_threePow_add_phi_dvd_at
    {e m x : ℕ}
    (hDiv :
      (2 : ℤ) ^ e ∣
        (3 : ℤ) ^ m * (x : ℤ) + criticalPrefixPhiZ m) :
    ((x : ℕ) : ZMod (2 ^ e)) =
      criticalXiTruncationClass e m := by
  have hDiv' :
      (((2 ^ e : ℕ) : ℤ)) ∣
        (3 : ℤ) ^ m * (x : ℤ) + criticalPrefixPhiZ m := by
    simpa using hDiv
  have hZero :
      (((
        (3 : ℤ) ^ m * (x : ℤ) + criticalPrefixPhiZ m : ℤ)) :
          ZMod (2 ^ e)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((3 : ℤ) ^ m * (x : ℤ) + criticalPrefixPhiZ m)
      (2 ^ e)).2 hDiv'
  push_cast at hZero
  have hMain :
      ((x : ℕ) : ZMod (2 ^ e)) =
        -(((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) *
          invThreePow e m) := by
    have hLinear :
        (3 : ZMod (2 ^ e)) ^ m *
            ((x : ℕ) : ZMod (2 ^ e)) =
          -((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) :=
      eq_neg_of_add_eq_zero_left hZero
    have hInv := threePow_mul_invThreePow e m
    calc
      ((x : ℕ) : ZMod (2 ^ e))
          = 1 * ((x : ℕ) : ZMod (2 ^ e)) := by simp
      _ =
          ((3 : ZMod (2 ^ e)) ^ m * invThreePow e m) *
            ((x : ℕ) : ZMod (2 ^ e)) := by
              rw [hInv]
      _ =
          ((3 : ZMod (2 ^ e)) ^ m *
              ((x : ℕ) : ZMod (2 ^ e))) *
            invThreePow e m := by
              ring
      _ =
          -((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) *
            invThreePow e m := by
              rw [hLinear]
      _ =
          -(((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) *
            invThreePow e m) := by
              ring
  calc
    ((x : ℕ) : ZMod (2 ^ e))
        = -(((criticalPrefixPhiZ m : ℤ) : ZMod (2 ^ e)) *
            invThreePow e m) := hMain
    _ = criticalXiTruncationClass e m :=
      (criticalXiTruncationClass_eq_neg_phi_mul_invThreePow e m).symm

/-! ## 2. actual single-corner entrance divisibility -/

namespace MinimalActualABObstructionPacket

/--
actual single-corner の入口 `b` では、affine numerator はまだ critical `Psi_b` だが、
prefix two-depth は `beta_b-1`。

従って入口で exact dyadic divisibility が成立する。
-/
theorem singleCorner_entrancePrefixDivisibility
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    (2 : ℤ) ^ (beattyIndex S.b - 1) ∣
      (3 : ℤ) ^ S.b *
          (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        criticalPrefixPhiZ S.b := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord

  have hmW : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using
      M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hbM : S.b < P.m :=
    lt_of_lt_of_le S.b_lt_c P.terminalCriticalStart_spec.1
  have hbLeW : S.b ≤ Collatz2.Word.oddSteps w := by
    rw [hmW]
    exact Nat.le_of_lt hbM

  have hActualCheckpoint :
      ∀ k : ℕ, k < S.b →
        Collatz2.Word.prefixTwoDepth w k = beattyIndex k := by
    intro k hkb
    have hkM : k < P.m := lt_trans hkb hbM
    have hCoord :=
      M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hkM
    have hLeft := S.left_checkpoint_eq_beatty hkb
    simpa [w, F, P] using hCoord.trans hLeft

  have hReal :
      Collatz2.Word.Realizes w
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [w] using
      FirstFailureEdge.upperExponentWord_realizesCanonical F
  have hDivNat :=
    wordPrefixDyadicDvdOfRealizes
      (w := w)
      (x := F.step.edge.upperR)
      (y := F.step.edge.upperR + F.upperNormalizedDefectNat)
      hReal hbLeW

  have hbLen : S.b ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hbLeW
  have hProfileAffine :
      profileAffineNumerator S.b (fun _ => 0) =
        Collatz2.Word.affineConst (w.take S.b) := by
    apply profileAffineNumerator_eq_affineConst_of_checkpoint
    · simp [Collatz2.Word.oddSteps, List.length_take_of_le hbLen]
    · intro k hk
      have hkb : k < S.b := hk
      have hTake :
          Collatz2.Word.prefixTwoDepth (w.take S.b) k =
            Collatz2.Word.prefixTwoDepth w k := by
        unfold Collatz2.Word.prefixTwoDepth
        rw [List.take_take]
        rw [min_eq_left (Nat.le_of_lt hkb)]
      unfold profileCheckpoint
      simp only [Nat.sub_zero]
      rw [hTake, hActualCheckpoint k hkb]
  have hZeroProfile :
      profileAffineNumerator S.b (fun _ => 0) =
        criticalPrefixPhiNat S.b := by
    unfold profileAffineNumerator criticalPrefixPhiNat profileCheckpoint
    simp
  have hAffineCritical :
      Collatz2.Word.affineConst (w.take S.b) =
        criticalPrefixPhiNat S.b :=
    hProfileAffine.symm.trans hZeroProfile

  have hCheckpointB :
      profileCheckpoint P.h S.b = beattyIndex S.b - 1 := by
    unfold profileCheckpoint
    rw [S.h_b_eq_one]
  have hCoordB :=
    M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hbM
  have hDepthB :
      Collatz2.Word.twoSteps (w.take S.b) =
        beattyIndex S.b - 1 := by
    change
      Collatz2.Word.prefixTwoDepth w S.b =
        beattyIndex S.b - 1
    simpa [w, F, P] using hCoordB.trans hCheckpointB

  rw [hDepthB, hAffineCritical] at hDivNat
  have hDivZ :
      (2 : ℤ) ^ (beattyIndex S.b - 1) ∣
        (3 : ℤ) ^ S.b * (F.step.edge.upperR : ℤ) +
          (criticalPrefixPhiNat S.b : ℤ) := by
    exact_mod_cast hDivNat
  rw [criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ] at hDivZ
  simpa [F] using hDivZ

/--
入口 divisibility を arbitrary-precision finite Xi class へ直結する。
-/
theorem singleCorner_entranceXiClass
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    ((M.actual.firstFailureEdge.step.edge.upperR : ℕ) :
        ZMod (2 ^ (beattyIndex S.b - 1))) =
      criticalXiTruncationClass
        (beattyIndex S.b - 1) S.b := by
  exact
    natCast_eq_criticalXi_of_threePow_add_phi_dvd_at
      (M.singleCorner_entrancePrefixDivisibility hL S)

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
