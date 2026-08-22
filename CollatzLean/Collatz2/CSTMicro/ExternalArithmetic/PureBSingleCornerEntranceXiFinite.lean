import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerEntranceXi
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerCardOne6466

set_option linter.style.nativeDecide false
set_option linter.style.emptyLine false
set_option exponentiation.threshold 4096

/-!
# Pure B single-corner: finite entrance Xi cutoff

入口 Xi bridge を finite side `m <= 6465` に適用する。

重要なのは `b=130,...,6465` を個別走査しないこと。
precision `e` 以上の Beatty term は `ZMod (2^e)` で消えるので、
`e <= beta_b` なら Xi truncation は index `b` 以降完全に freeze する。

まず executable `(m,beta,Psi)` recurrence を一度だけ certified し、

  beta_130 = 206,
  Xi_205(130) > 16384 * 6466^15

を ground native computation で固定する。すると `b>=130` の全てが同じ
`Xi_205(130)` class に落ち、actual representative の Rhin bound と矛盾する。
従って `m<=6465` では `b<130`。

さらに exact BHZ `m-b<=2155` と合わせて `m<=2284`。
同じ argument を `(e,b)=(182,116)` でもう一度行い、
最終的に

  b < 116,
  m <= 2270

まで削る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. executable critical `(m,beta,Psi)` state -/

private structure EntranceXiScanState where
  m : ℕ
  beta : ℕ
  phi : ℕ
deriving Inhabited

private def entranceXiScanInitial : EntranceXiScanState := {
  m := 0
  beta := 0
  phi := 0
}

/-- Beatty increment は exact に 1 または 2。 -/
private def EntranceXiScanState.nextBeta
    (S : EntranceXiScanState) : ℕ :=
  if 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) then
    S.beta + 1
  else
    S.beta + 2

/-- `Psi_(m+1)=3 Psi_m+2^beta_m` と同時に一 step 進める。 -/
private def EntranceXiScanState.next
    (S : EntranceXiScanState) : EntranceXiScanState := {
  m := S.m + 1
  beta := S.nextBeta
  phi := 3 * S.phi + 2 ^ S.beta
}

private def entranceXiStateAt : ℕ → EntranceXiScanState
  | 0 => entranceXiScanInitial
  | n + 1 => (entranceXiStateAt n).next

@[simp] private theorem entranceXiStateAt_m
    (n : ℕ) :
    (entranceXiStateAt n).m = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [entranceXiStateAt, EntranceXiScanState.next, ih]

/-- proof-oriented objects との semantic invariant。 -/
private def EntranceXiScanState.Correct
    (S : EntranceXiScanState) : Prop :=
  S.beta = beattyIndex S.m ∧
    ∀ e : ℕ,
      (S.phi : ZMod (2 ^ e)) =
        (3 : ZMod (2 ^ e)) ^ S.m *
          beattyInverseContribution e S.m

private theorem entranceXiScanInitial_correct :
    entranceXiScanInitial.Correct := by
  constructor
  · simp [entranceXiScanInitial]
  · intro e
    simp only [
      entranceXiScanInitial,
      Nat.cast_zero,
      pow_zero,
      beattyInverseContribution_zero,
      mul_zero
    ]

/-- executable `nextBeta` は proof-oriented Beatty index と exact に一致する。 -/
private theorem EntranceXiScanState.nextBeta_eq
    {S : EntranceXiScanState}
    (hS : S.Correct) :
    S.nextBeta = beattyIndex (S.m + 1) := by
  have hBeta : S.beta = beattyIndex S.m := hS.1
  have hStrict0 := beattyIndex_lt_succ S.m
  have hStrict :
      S.beta < beattyIndex (S.m + 1) := by
    simpa [hBeta] using hStrict0
  have hLower :
      S.beta + 1 ≤ beattyIndex (S.m + 1) := by
    omega

  have hUpperM := beattyIndex_upper S.m
  rw [← hBeta] at hUpperM
  have hCandidate :
      3 ^ (S.m + 1) ≤ 2 ^ ((S.beta + 2) + 1) := by
    rw [pow_succ]
    calc
      3 ^ S.m * 3
          ≤ 2 ^ (S.beta + 1) * 3 :=
        Nat.mul_le_mul_right 3 hUpperM
      _ ≤ 2 ^ (S.beta + 1) * 4 := by
        exact
          Nat.mul_le_mul_left
            (2 ^ (S.beta + 1))
            (by norm_num : 3 ≤ 4)
      _ = 2 ^ ((S.beta + 2) + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  have hUpper :
      beattyIndex (S.m + 1) ≤ S.beta + 2 :=
    beattyIndex_le_of_upper hCandidate

  by_cases hOne :
      3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2)
  · have hAtOne :
        beattyIndex (S.m + 1) ≤ S.beta + 1 := by
      apply beattyIndex_le_of_upper
      simpa [Nat.add_assoc] using hOne
    have hEq :
        beattyIndex (S.m + 1) = S.beta + 1 := by
      omega
    simp [EntranceXiScanState.nextBeta, hOne, hEq]
  · have hNe :
        beattyIndex (S.m + 1) ≠ S.beta + 1 := by
      intro hEq
      have hU := beattyIndex_upper (S.m + 1)
      rw [hEq] at hU
      apply hOne
      simpa [Nat.add_assoc] using hU
    have hEq :
        beattyIndex (S.m + 1) = S.beta + 2 := by
      omega
    simp [EntranceXiScanState.nextBeta, hOne, hEq]

/-- semantic invariant は一 step で保存される。 -/
private theorem EntranceXiScanState.next_correct
    {S : EntranceXiScanState}
    (hS : S.Correct) :
    S.next.Correct := by
  constructor
  · exact S.nextBeta_eq hS
  · intro e
    have hPhi := hS.2 e
    have hInv := threePow_mul_invThreePow e (S.m + 1)
    have hTerm :
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
            ((2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
              invThreePow e (S.m + 1)) =
          (2 : ZMod (2 ^ e)) ^ beattyIndex S.m := by
      calc
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
              ((2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
                invThreePow e (S.m + 1))
            =
          (2 : ZMod (2 ^ e)) ^ beattyIndex S.m *
            ((3 : ZMod (2 ^ e)) ^ (S.m + 1) *
              invThreePow e (S.m + 1)) := by
                ring
        _ = (2 : ZMod (2 ^ e)) ^ beattyIndex S.m := by
              rw [hInv]
              ring
    change
      ((3 * S.phi + 2 ^ S.beta : ℕ) : ZMod (2 ^ e)) =
        (3 : ZMod (2 ^ e)) ^ (S.m + 1) *
          beattyInverseContribution e (S.m + 1)
    push_cast
    rw [beattyInverseContribution_succ, mul_add, hTerm]
    rw [hPhi, hS.1, pow_succ]
    ring

private theorem entranceXiStateAt_correct
    (n : ℕ) :
    (entranceXiStateAt n).Correct := by
  induction n with
  | zero => exact entranceXiScanInitial_correct
  | succ n ih => exact EntranceXiScanState.next_correct ih

/-- state から fixed precision `e` の Xi class を読む。 -/
private def EntranceXiScanState.residueClass
    (S : EntranceXiScanState)
    (e : ℕ) : ZMod (2 ^ e) :=
  (-(S.phi : ZMod (2 ^ e))) * invThreePow e S.m

private def EntranceXiScanState.residue
    (S : EntranceXiScanState)
    (e : ℕ) : ℕ :=
  (S.residueClass e).val

private theorem EntranceXiScanState.residueClass_eq_xi
    {S : EntranceXiScanState}
    (hS : S.Correct)
    (e : ℕ) :
    S.residueClass e =
      criticalXiTruncationClass e S.m := by
  have hPhi := hS.2 e
  have hInv := threePow_mul_invThreePow e S.m
  unfold EntranceXiScanState.residueClass
  unfold criticalXiTruncationClass
  rw [hPhi]
  calc
    (-((3 : ZMod (2 ^ e)) ^ S.m *
          beattyInverseContribution e S.m)) *
        invThreePow e S.m
        =
      - beattyInverseContribution e S.m *
        ((3 : ZMod (2 ^ e)) ^ S.m * invThreePow e S.m) := by
          ring
    _ = - beattyInverseContribution e S.m := by
          rw [hInv]
          ring

private theorem EntranceXiScanState.residue_eq_xi
    {S : EntranceXiScanState}
    (hS : S.Correct)
    (e : ℕ) :
    S.residue e =
      (criticalXiTruncationClass e S.m).val := by
  exact congrArg ZMod.val (S.residueClass_eq_xi hS e)

/-! ## 2. Beatty tail は fixed precision で freeze する -/

private theorem beattyIndex_mono_of_le_entranceXi
    {a b : ℕ}
    (hab : a ≤ b) :
    beattyIndex a ≤ beattyIndex b := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · exact Nat.le_of_lt (beattyIndex_strictMono hlt)
  · exact le_rfl

/-- `e<=q` なら `2^q=0` in `ZMod(2^e)`。 -/
private theorem two_pow_eq_zero_zmod_of_le
    {e q : ℕ}
    (heq : e ≤ q) :
    (2 : ZMod (2 ^ e)) ^ q = 0 := by
  exact ZMod.natCast_pow_eq_zero_of_le 2 heq

/--
`e<=beta_b` なら index `b` 以降に追加される Beatty terms は全て 0。
従って arbitrary later truncation は `b` で freeze する。
-/
theorem criticalXiTruncationClass_eq_of_tail_above_precision
    {e b m : ℕ}
    (hbm : b ≤ m)
    (hBeta : e ≤ beattyIndex b) :
    criticalXiTruncationClass e m =
      criticalXiTruncationClass e b := by
  unfold criticalXiTruncationClass
  congr 1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbm
  induction d with
  | zero => rfl
  | succ d ih =>
      have hIndex : b + (d + 1) = (b + d) + 1 := by omega
      rw [hIndex, beattyInverseContribution_succ]
      have hMono : beattyIndex b ≤ beattyIndex (b + d) :=
        beattyIndex_mono_of_le_entranceXi (by omega)
      have hPowZero :
          (2 : ZMod (2 ^ e)) ^ beattyIndex (b + d) = 0 :=
        two_pow_eq_zero_zmod_of_le (le_trans hBeta hMono)
      rw [hPowZero, zero_mul, add_zero]
      exact ih (by omega)

/-! ## 3. frozen ground certificates at 130 and 116 -/

private theorem entranceXiStateAt_130_beta :
    (entranceXiStateAt 130).beta = 206 := by
  native_decide

/-- executable recurrence から `beta_130=206` を certified。 -/
theorem beattyIndex_130_eq_206 :
    beattyIndex 130 = 206 := by
  have hCorrect := entranceXiStateAt_correct 130
  have hBeta :
      (entranceXiStateAt 130).beta = beattyIndex 130 := by
    have h := hCorrect.1
    rw [entranceXiStateAt_m 130] at h
    exact h
  calc
    beattyIndex 130 = (entranceXiStateAt 130).beta := hBeta.symm
    _ = 206 := entranceXiStateAt_130_beta

private theorem entranceXiStateAt_116_beta :
    (entranceXiStateAt 116).beta = 183 := by
  native_decide

/-- executable recurrence から `beta_116=183` を certified。 -/
theorem beattyIndex_116_eq_183 :
    beattyIndex 116 = 183 := by
  have hCorrect := entranceXiStateAt_correct 116
  have hBeta :
      (entranceXiStateAt 116).beta = beattyIndex 116 := by
    have h := hCorrect.1
    rw [entranceXiStateAt_m 116] at h
    exact h
  calc
    beattyIndex 116 = (entranceXiStateAt 116).beta := hBeta.symm
    _ = 183 := entranceXiStateAt_116_beta

private theorem entranceXiStateAt_130_residue205_gt_6465Bound :
    rhinGapK * 6466 ^ 15 <
      (entranceXiStateAt 130).residue 205 := by
  native_decide

/--
205-bit frozen Xi residue は `m<=6465` の actual Rhin representative bound より大きい。
-/
theorem criticalXi205_130_gt_6465Bound :
    rhinGapK * 6466 ^ 15 <
      (criticalXiTruncationClass 205 130).val := by
  let S := entranceXiStateAt 130
  have hCorrect : S.Correct := by
    simpa [S] using entranceXiStateAt_correct 130
  have hResidue := S.residue_eq_xi hCorrect 205
  have hM : S.m = 130 := by simp [S]
  rw [hM] at hResidue
  have hGround :
      rhinGapK * 6466 ^ 15 < S.residue 205 := by
    simpa [S] using entranceXiStateAt_130_residue205_gt_6465Bound
  rw [hResidue] at hGround
  exact hGround

private theorem entranceXiStateAt_116_residue182_gt_2284Bound :
    rhinGapK * 2285 ^ 15 <
      (entranceXiStateAt 116).residue 182 := by
  native_decide

/--
182-bit frozen Xi residue は `m<=2284` の actual Rhin representative bound より大きい。
-/
theorem criticalXi182_116_gt_2284Bound :
    rhinGapK * 2285 ^ 15 <
      (criticalXiTruncationClass 182 116).val := by
  let S := entranceXiStateAt 116
  have hCorrect : S.Correct := by
    simpa [S] using entranceXiStateAt_correct 116
  have hResidue := S.residue_eq_xi hCorrect 182
  have hM : S.m = 116 := by simp [S]
  rw [hM] at hResidue
  have hGround :
      rhinGapK * 2285 ^ 15 < S.residue 182 := by
    simpa [S] using entranceXiStateAt_116_residue182_gt_2284Bound
  rw [hResidue] at hGround
  exact hGround

/-! ## 4. actual finite-side consequences -/

namespace MinimalActualABObstructionPacket

private theorem pow_dvd_pow_of_le_int
    {a b : ℕ}
    (hab : a ≤ b) :
    (2 : ℤ) ^ a ∣ (2 : ℤ) ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  refine ⟨(2 : ℤ) ^ d, ?_⟩
  rw [pow_add]

/-- `m<=6465` なら actual representative は frozen finite bound 以下。 -/
theorem actualRepresentative_le_6465Bound
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    M.actual.firstFailureEdge.step.edge.upperR ≤
      rhinGapK * 6466 ^ 15 := by
  have hR := M.actualRepresentative_le_rhinPolynomial R hL
  have hm1 :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 6466 := by
    omega
  have hPow :
      ((M.toPureBProfileObstruction hL).m + 1) ^ 15 ≤
        6466 ^ 15 :=
    Nat.pow_le_pow_left hm1 15
  exact le_trans hR (Nat.mul_le_mul_left rhinGapK hPow)

/--
`b ≥ 130` なら、entrance depth `beattyIndex b - 1` は
precision `205` 以上に達している。
-/
theorem beattyIndex_sub_one_ge_205_of_130_le
    {b : ℕ}
    (hb130 : 130 ≤ b) :
    205 ≤ beattyIndex b - 1 := by
  have hMono :
      beattyIndex 130 ≤ beattyIndex b :=
    beattyIndex_mono_of_le_entranceXi hb130
  rw [beattyIndex_130_eq_206] at hMono
  omega

/--
`b ≥ 130` の actual single-corner entrance では、
既存の entrance divisibility を precision `205` まで降ろせる。
-/
theorem singleCorner_entrancePrefixDivisibility_205
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hb130 : 130 ≤ S.b) :
    (2 : ℤ) ^ 205 ∣
      (3 : ℤ) ^ S.b *
          (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        criticalPrefixPhiZ S.b := by
  have hPrecision :
      205 ≤ beattyIndex S.b - 1 :=
    beattyIndex_sub_one_ge_205_of_130_le hb130

  have hDivHigh :=
    M.singleCorner_entrancePrefixDivisibility hL S

  have hPowDvd :
      (2 : ℤ) ^ 205 ∣
        (2 : ℤ) ^ (beattyIndex S.b - 1) :=
    pow_dvd_pow_of_le_int hPrecision

  exact dvd_trans hPowDvd hDivHigh

/--
precision `205` では、index `130` 以降の critical Xi truncation class は
index `130` の residue に freeze する。
-/
theorem criticalXiTruncationClass_205_eq_130_of_130_le
    {b : ℕ}
    (hb130 : 130 ≤ b) :
    criticalXiTruncationClass 205 b =
      criticalXiTruncationClass 205 130 := by
  exact
    criticalXiTruncationClass_eq_of_tail_above_precision
      hb130
      (by
        rw [beattyIndex_130_eq_206]
        omega)

/--
`b ≥ 130` の actual single-corner entrance residue は、
precision `205` で index `130` の frozen Xi residue に一致する。
-/
theorem singleCorner_entranceClass205_eq_Xi130
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hb130 : 130 ≤ S.b) :
    ((M.actual.firstFailureEdge.step.edge.upperR : ℕ) :
        ZMod (2 ^ 205)) =
      criticalXiTruncationClass 205 130 := by
  have hDiv205 :=
    singleCorner_entrancePrefixDivisibility_205
      M hL S hb130

  have hXi205 :=
    natCast_eq_criticalXi_of_threePow_add_phi_dvd_at hDiv205

  have hFreeze :
      criticalXiTruncationClass 205 S.b =
        criticalXiTruncationClass 205 130 :=
    criticalXiTruncationClass_205_eq_130_of_130_le hb130

  rw [hFreeze] at hXi205
  exact hXi205

/--
finite range `m ≤ 6465` で使う actual Rhin bound は
precision `205` の modulus より小さい。
-/
theorem actualRepresentative_lt_pow205_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    M.actual.firstFailureEdge.step.edge.upperR < 2 ^ 205 := by
  have hRBound :=
    M.actualRepresentative_le_6465Bound R hL hm

  have hModulusBound :
      rhinGapK * 6466 ^ 15 < 2 ^ 205 := by
    native_decide

  exact lt_of_le_of_lt hRBound hModulusBound

/--
finite range `m ≤ 6465` では actual representative は
precision `205` の frozen Xi residue at `130` より真に小さい。
-/
theorem actualRepresentative_lt_Xi205_130_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    M.actual.firstFailureEdge.step.edge.upperR <
      (criticalXiTruncationClass 205 130).val := by
  have hRBound :=
    M.actualRepresentative_le_6465Bound R hL hm

  have hXiBound :=
    criticalXi205_130_gt_6465Bound

  omega

/--
finite side `m ≤ 6465` では single-corner entrance は `b < 130`。

`b ≥ 130` なら precision `205` で entrance residue が
index `130` の frozen Xi residue に一致する。
一方 finite Rhin bound では actual representative はその residue より小さいため、
両者は一致できない。
-/
theorem singleCorner_b_lt_130_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    S.b < 130 := by
  by_contra hnot

  have hb130 : 130 ≤ S.b := by
    omega

  have hXiEq :
      ((M.actual.firstFailureEdge.step.edge.upperR : ℕ) :
          ZMod (2 ^ 205)) =
        criticalXiTruncationClass 205 130 :=
    singleCorner_entranceClass205_eq_Xi130
      M hL S hb130

  have hRLtMod :
      M.actual.firstFailureEdge.step.edge.upperR < 2 ^ 205 :=
    actualRepresentative_lt_pow205_of_m_le_6465
      R M hL hm

  have hRVal :
      (((M.actual.firstFailureEdge.step.edge.upperR : ℕ) :
          ZMod (2 ^ 205))).val =
        M.actual.firstFailureEdge.step.edge.upperR := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hRLtMod

  have hVal :=
    congrArg ZMod.val hXiEq

  rw [hRVal] at hVal

  have hStrict :
      M.actual.firstFailureEdge.step.edge.upperR <
        (criticalXiTruncationClass 205 130).val :=
    actualRepresentative_lt_Xi205_130_of_m_le_6465
      R M hL hm

  omega

/-- `b<130` と exact BHZ `m-b<=2155` から `m<=2284`。 -/
theorem singleCorner_m_le_2284_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    (M.toPureBProfileObstruction hL).m ≤ 2284 := by
  have hb : S.b < 130 :=
    M.singleCorner_b_lt_130_of_m_le_6465 R hL S hm
  have hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ 13 := by
    norm_num
    omega
  have hWidth :=
    M.singleCorner_m_sub_b_le_2155_of_ell_thirteen
      R hL S hmSize
  have hbM :
      S.b ≤ (M.toPureBProfileObstruction hL).m :=
    le_trans (Nat.le_of_lt S.b_lt_c)
      (M.toPureBProfileObstruction hL).terminalCriticalStart_spec.1
  omega

/-- `m<=2284` なら actual representative は第2 frozen bound 以下。 -/
theorem actualRepresentative_le_2284Bound
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 2284) :
    M.actual.firstFailureEdge.step.edge.upperR ≤
      rhinGapK * 2285 ^ 15 := by
  have hR := M.actualRepresentative_le_rhinPolynomial R hL
  have hm1 :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2285 := by
    omega
  have hPow :
      ((M.toPureBProfileObstruction hL).m + 1) ^ 15 ≤
        2285 ^ 15 :=
    Nat.pow_le_pow_left hm1 15
  exact le_trans hR (Nat.mul_le_mul_left rhinGapK hPow)

/--
第2 frozen Xi cutoff。`m<=6465` なら実際には `b<116` まで下がる。
-/
theorem singleCorner_b_lt_116_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    S.b < 116 := by
  have hm2284 :=
    M.singleCorner_m_le_2284_of_m_le_6465 R hL S hm
  by_contra hnot
  have hb116 : 116 ≤ S.b := by omega
  have hBetaMono : beattyIndex 116 ≤ beattyIndex S.b :=
    beattyIndex_mono_of_le_entranceXi hb116
  rw [beattyIndex_116_eq_183] at hBetaMono
  have hPrecision :
      182 ≤ beattyIndex S.b - 1 := by
    omega

  have hDivHigh := M.singleCorner_entrancePrefixDivisibility hL S
  have hPowDvd :
      (2 : ℤ) ^ 182 ∣
        (2 : ℤ) ^ (beattyIndex S.b - 1) :=
    pow_dvd_pow_of_le_int hPrecision
  have hDiv182 :
      (2 : ℤ) ^ 182 ∣
        (3 : ℤ) ^ S.b *
            (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          criticalPrefixPhiZ S.b :=
    dvd_trans hPowDvd hDivHigh
  have hXi182 :=
    natCast_eq_criticalXi_of_threePow_add_phi_dvd_at hDiv182
  have hFreeze :
      criticalXiTruncationClass 182 S.b =
        criticalXiTruncationClass 182 116 :=
    criticalXiTruncationClass_eq_of_tail_above_precision
      hb116
      (by rw [beattyIndex_116_eq_183]; omega)
  rw [hFreeze] at hXi182

  have hRBound := M.actualRepresentative_le_2284Bound R hL hm2284
  have hXiBound := criticalXi182_116_gt_2284Bound
  have hModulusBound :
      rhinGapK * 2285 ^ 15 < 2 ^ 182 := by
    native_decide
  have hRLtMod :
      M.actual.firstFailureEdge.step.edge.upperR < 2 ^ 182 :=
    lt_of_le_of_lt hRBound hModulusBound
  have hVal := congrArg ZMod.val hXi182
  have hRVal :
      (((M.actual.firstFailureEdge.step.edge.upperR : ℕ) :
          ZMod (2 ^ 182))).val =
        M.actual.firstFailureEdge.step.edge.upperR := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hRLtMod
  rw [hRVal] at hVal
  omega

/-- 第2 cutoff と exact BHZ を合わせると finite residue は `m<=2270`。 -/
theorem singleCorner_m_le_2270_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    (M.toPureBProfileObstruction hL).m ≤ 2270 := by
  have hb : S.b < 116 :=
    M.singleCorner_b_lt_116_of_m_le_6465 R hL S hm
  have hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ 13 := by
    norm_num
    omega
  have hWidth :=
    M.singleCorner_m_sub_b_le_2155_of_ell_thirteen
      R hL S hmSize
  have hbM :
      S.b ≤ (M.toPureBProfileObstruction hL).m :=
    le_trans (Nat.le_of_lt S.b_lt_c)
      (M.toPureBProfileObstruction hL).terminalCriticalStart_spec.1
  omega

/--
cardinality-one actual branch の finite residueを packet construction まで含めて公開する。
`m<=6465` なら `m<=2270`。
-/
theorem singleCorner_card_one_m_le_2270_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    (hm : (M.toPureBProfileObstruction hL).m ≤ 6465) :
    (M.toPureBProfileObstruction hL).m ≤ 2270 := by
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  exact M.singleCorner_m_le_2270_of_m_le_6465 R hL S hm

/--
large-side `m>=6466` elimination と finite entrance-Xi cutoff を合成する最終 card-one bound。
追加の `m` hypothesis は不要で、actual cardinality-one obstruction は必ず `m<=2270`。
-/
theorem singleCorner_card_one_m_le_2270
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.toPureBProfileObstruction hL).m ≤ 2270 := by
  by_cases hmLarge :
      6466 ≤ (M.toPureBProfileObstruction hL).m
  · exact False.elim
      (M.singleCorner_card_one_impossible_of_m_ge_6466
        R hL hCard hmLarge)
  · have hmSmall :
        (M.toPureBProfileObstruction hL).m ≤ 6465 := by
      omega
    exact
      M.singleCorner_card_one_m_le_2270_of_m_le_6465
        R hL hCard hmSmall

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
