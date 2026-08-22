import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerFiniteHenselScan
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerWholeRunDyadic
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: finite Hensel scan -> complete elimination

前段までで actual cardinality-one branch は

  m <= 2270,
  b < 116,
  width = c-b <= 213

へ落ちた。

`PureBSingleCornerFiniteHenselScan` はこの箱の全 straight-corner model について、
critical suffix を rank 130 までだけ直接 Hensel scan する。

rank 130 以降では `beta_130 = 206` なので Hensel lift は representative の
下位 205 bit を変えない。そこで native certificate は長い tail を走査せず、

  R mod 2^205 > rhinGapK * 2271^15

という frozen residue を返す。

このファイルでは最後の soundness bridge を作る。

1. actual single-corner profile の `c` までの affine numerator が scanner の初期値と一致。
2. `[c,m)` は critical suffix なので scanner の recurrence と actual affine numerator が一致。
3. scanner final representative `R` と actual upper representative `R_B` は、同じ
   `2^(beta_m+1)` affine congruence の canonical representative なので一致。
4. `m < 130` なら短い prefix scan から final state の `q < R` を直接読む。
5. `130 <= m` なら 205-bit residue は freeze point から final state まで不変。
   actual `R_B <= rhinGapK * 2271^15 < 2^205` と frozen residue certificate が矛盾する。
6. 残る small-rank case では actual first-failure endpoint
   `R_B + q_B` により `q >= R_B` となり、prefix safety `q < R_B` と矛盾する。

従って actual minimal B obstruction の `card = 1` branch は完全に消える。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-! ## 1. straight interval の exact affine start -/

/-- scanner の geometric accumulator は期待する finite sum。 -/
theorem singleCornerTwoThreeSum_eq_sum
    (n : ℕ) :
    singleCornerTwoThreeSum n =
      Finset.sum (Finset.range n)
        (fun i => 2 ^ i * 3 ^ (n - (i + 1))) := by
  induction n with
  | zero => simp [singleCornerTwoThreeSum]
  | succ n ih =>
      rw [singleCornerTwoThreeSum, Finset.sum_range_succ]
      have hPrefix :
          Finset.sum (Finset.range n)
              (fun i => 2 ^ i * 3 ^ (n + 1 - (i + 1))) =
            3 *
              Finset.sum (Finset.range n)
                (fun i => 2 ^ i * 3 ^ (n - (i + 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < n := Finset.mem_range.mp hi
        have hExp :
            n + 1 - (i + 1) = (n - (i + 1)) + 1 := by
          omega
        rw [hExp, pow_succ]
        ring
      rw [hPrefix, ← ih]
      have hLast : n + 1 - (n + 1) = 0 := by omega
      rw [hLast, pow_zero, mul_one]

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/--
actual single-corner entrance は critical Beatty jump `+2` の位置。
-/
theorem beatty_entrance_jump_two
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    beattyIndex S.b = beattyIndex (S.b - 1) + 2 := by
  have hbPos : 0 < S.b := S.b_pos
  have hcLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le S.b_lt_c hcLe
  have hbOneLe : 1 ≤ S.b := by omega
  have hPrevM : S.b - 1 < P.m := by omega
  have hPrevZero : P.h (S.b - 1) = 0 := by
    apply S.depth_eq_zero_of_outside hPrevM
    left
    omega
  have hStrict0 :=
    P.admissible.checkpoint_strict
      (k := S.b - 1)
      (by simpa [Nat.sub_add_cancel hbOneLe] using hbM)
  have hStrict :
      beattyIndex (S.b - 1) < beattyIndex S.b - 1 := by
    simpa [
      profileCheckpoint,
      hPrevZero,
      S.h_b_eq_one,
      Nat.sub_add_cancel hbOneLe
    ] using hStrict0
  have hLower :
      beattyIndex (S.b - 1) + 2 ≤ beattyIndex S.b := by
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbPos)
  have hbEq : S.b = j + 1 := hj
  have hState := singleCornerCriticalStateAt_correct j
  have hBeta :
      (singleCornerCriticalStateAt j).beta =
        beattyIndex j := by
    simpa using hState.1
  have hNext :
      (singleCornerCriticalStateAt j).nextBeta =
        beattyIndex (j + 1) := by
    have h :=
      SingleCornerCriticalState.nextBeta_eq hState
    simpa using h
  have hAtSucc :
      beattyIndex (j + 1) ≤ beattyIndex j + 2 := by
    have hForm :
        (singleCornerCriticalStateAt j).nextBeta =
            (singleCornerCriticalStateAt j).beta + 1 ∨
        (singleCornerCriticalStateAt j).nextBeta =
            (singleCornerCriticalStateAt j).beta + 2 := by
      unfold SingleCornerCriticalState.nextBeta
      split <;> simp
    rw [hNext, hBeta] at hForm
    omega
  rw [hbEq, show (j + 1) - 1 = j by omega] at hLower ⊢
  omega

/-- scanner の executable entrance test は actual `b` で true。 -/
theorem henselEntranceBool_eq_true
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    singleCornerHenselEntranceBool S.b = true := by
  have hbPos := S.b_pos
  have hJump := S.beatty_entrance_jump_two
  have hB := singleCornerCriticalStateAt_correct S.b
  have hPrev := singleCornerCriticalStateAt_correct (S.b - 1)
  have hExec :
      (singleCornerCriticalStateAt S.b).beta =
        (singleCornerCriticalStateAt (S.b - 1)).beta + 2 := by
    rw [hB.1, hPrev.1]
    simpa only [singleCornerCriticalStateAt_m] using hJump
  simp [singleCornerHenselEntranceBool, Nat.ne_of_gt hbPos, hExec]

/--
scanner 初期 geometric interval `[b,c)` の affine numerator は actual profile の
`c`-prefix affine numeratorそのもの。
-/
theorem profileAffineNumerator_terminalStart_eq_henselInitial
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket) :
    profileAffineNumerator P.terminalCriticalStart P.h =
      singleCornerInitialAffine
        (singleCornerCriticalStateAt S.b)
        S.width := by
  let b := S.b
  let n := S.width
  let c := P.terminalCriticalStart
  have hbLtC : b < c := by simpa [b, c] using S.b_lt_c
  have hcEq : c = b + n := by
    have h := S.b_add_width_eq_terminalStart
    simpa [b, c, n] using h.symm
  have hcLeM : c ≤ P.m := P.terminalCriticalStart_spec.1
  have hbM : b < P.m := lt_of_lt_of_le hbLtC hcLeM
  have hBState := singleCornerCriticalStateAt_correct b
  unfold profileAffineNumerator
  change
    (∑ k ∈ Finset.range c,
      2 ^ profileCheckpoint P.h k *
        3 ^ (c - (k + 1))) =
      singleCornerInitialAffine
        (singleCornerCriticalStateAt b) n

  rw [hcEq, Finset.sum_range_add]

  have hLeft :
      Finset.sum (Finset.range b)
          (fun k =>
            2 ^ profileCheckpoint P.h k *
              3 ^ (b + n - (k + 1))) =
        3 ^ n * criticalPrefixPhiNat b := by
    unfold criticalPrefixPhiNat
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hkMem
    have hkb : k < b := Finset.mem_range.mp hkMem
    have hkM : k < P.m := lt_trans hkb hbM
    have hZero := S.depth_eq_zero_of_outside hkM (Or.inl hkb)
    have hExp :
        b + n - (k + 1) = n + (b - (k + 1)) := by
      omega
    unfold profileCheckpoint
    rw [hZero, Nat.sub_zero, hExp, pow_add]
    ring

  have hMiddle :
      Finset.sum (Finset.range n)
          (fun i =>
            2 ^ profileCheckpoint P.h (b + i) *
              3 ^ (b + n - (b + i + 1))) =
        2 ^ (beattyIndex b - 1) * singleCornerTwoThreeSum n := by
    rw [singleCornerTwoThreeSum_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hiMem
    have hiN : i < n := Finset.mem_range.mp hiMem
    have hbiC : b + i < c := by
      rw [hcEq]
      omega
    have hLine := S.checkpoint_line (b + i) (by omega) (by simpa [c] using hbiC)
    have hDiff : b + i - S.b = i := by
      dsimp [b]
      omega
    have hCheckpoint :
        profileCheckpoint P.h (b + i) = beattyIndex b - 1 + i := by
      simpa [b, hDiff] using hLine
    have hExp : b + n - (b + i + 1) = n - (i + 1) := by omega
    rw [hCheckpoint, hExp, pow_add]
    ring

  rw [hLeft, hMiddle]
  unfold singleCornerInitialAffine
  rw [hBState.1, hBState.2.1]
  simp

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-! ## 2. critical suffix recurrence = profile affine recurrence -/

/-- depth zero の新 endpoint を一つ追加すると affine numerator は critical recurrence。 -/
theorem profileAffineNumerator_succ_of_depth_zero
    (h : ℕ → ℕ)
    (r : ℕ)
    (hZero : h r = 0) :
    profileAffineNumerator (r + 1) h =
      3 * profileAffineNumerator r h + 2 ^ beattyIndex r := by
  classical
  unfold profileAffineNumerator
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range r)
          (fun k =>
            2 ^ profileCheckpoint h k *
              3 ^ (r + 1 - (k + 1))) =
        3 *
          Finset.sum (Finset.range r)
            (fun k =>
              2 ^ profileCheckpoint h k *
                3 ^ (r - (k + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkR : k < r := Finset.mem_range.mp hk
    have hExp : r + 1 - (k + 1) = (r - (k + 1)) + 1 := by omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLastExp : r + 1 - (r + 1) = 0 := by omega
  rw [hLastExp, pow_zero, mul_one]
  unfold profileCheckpoint
  rw [hZero, Nat.sub_zero]

/--
Hensel iterate の stored affine numerator は terminal critical suffix に沿って
actual profile numerator と exact に一致し続ける。
-/
theorem henselIterate_A_eq_profileAffine
    {P : PureBProfileObstruction}
    {c : ℕ}
    (hSuffix : IsTerminalCriticalSuffix P c)
    {S0 : SingleCornerHenselState}
    (hCorrect : S0.Correct)
    (hm : S0.m = c)
    (hA : S0.A = profileAffineNumerator c P.h)
    (d : ℕ)
    (hEnd : c + d ≤ P.m) :
    (SingleCornerHenselState.iterate d S0).A =
      profileAffineNumerator (c + d) P.h := by
  induction d generalizing c S0 with
  | zero =>
      simpa [SingleCornerHenselState.iterate] using hA
  | succ d ih =>
      have hcLtM : c < P.m := by omega
      have hZero : P.h c = 0 :=
        hSuffix.2 c le_rfl hcLtM
      have hRec :=
        profileAffineNumerator_succ_of_depth_zero P.h c hZero

      have hNextCorrect : S0.next.Correct :=
        SingleCornerHenselState.next_correct hCorrect
      have hNextM : S0.next.m = c + 1 := by
        simp [SingleCornerHenselState.next, hm]
      have hNextA :
          S0.next.A = profileAffineNumerator (c + 1) P.h := by
        change 3 * S0.A + 2 ^ S0.beta = profileAffineNumerator (c + 1) P.h
        rw [hA]
        have hBeta : S0.beta = beattyIndex c := by
          rw [hCorrect.1, hm]
        rw [hBeta]
        exact hRec.symm
      have hSuffix' : IsTerminalCriticalSuffix P (c + 1) := by
        refine ⟨by omega, ?_⟩
        intro k hck hkM
        exact hSuffix.2 k (by omega) hkM
      have hIH :=
        ih hSuffix' hNextCorrect hNextM hNextA (by omega)
      change
        (SingleCornerHenselState.iterate d S0.next).A =
          profileAffineNumerator (c + (d + 1)) P.h
      have hIndex :
          c + 1 + d = c + (d + 1) := by
        omega
      rw [← hIndex]
      exact hIH

/-! ## 3. actual packet is one of the certified candidates -/

namespace MinimalActualABObstructionPacket

/--
actual card-one candidate の corner 終端 `c` における scanner 初期 state。

この state から rank 130 までは短い safety scan を行い、
それより右では 205-bit frozen residue を使う。
-/
noncomputable def singleCornerCertifiedStartState
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    SingleCornerHenselState := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let c := P.terminalCriticalStart
  let B := singleCornerCriticalStateAt S.b
  let C := singleCornerCriticalStateAt c
  let A := singleCornerInitialAffine B S.width
  exact SingleCornerHenselState.init C A

/--
actual candidate を rank `max(c,130)` まで進めた frozen state。
`c < 130` なら rank 130、`c ≥ 130` なら start state 自身である。
-/
noncomputable def singleCornerCertifiedFreezeState
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    SingleCornerHenselState :=
  let P := M.toPureBProfileObstruction hL
  SingleCornerHenselState.iterate
    (130 - P.terminalCriticalStart)
    (M.singleCornerCertifiedStartState R hL hCard)

/--
actual card-one candidate の final Hensel state。
初期 state を一度だけ固定し、actual rank `m` まで iterate する。
-/
noncomputable def singleCornerCertifiedFinalState
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    SingleCornerHenselState :=
  let P := M.toPureBProfileObstruction hL
  SingleCornerHenselState.iterate
    (P.m - P.terminalCriticalStart)
    (M.singleCornerCertifiedStartState R hL hCard)

/-- actual card-one start satisfies executable entrance equality。 -/
theorem singleCorner_actual_henselEntrance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    (singleCornerCriticalStateAt S.b).beta =
      (singleCornerCriticalStateAt (S.b - 1)).beta + 2 := by
  have hJump := S.beatty_entrance_jump_two
  have hB := singleCornerCriticalStateAt_correct S.b
  have hPrev := singleCornerCriticalStateAt_correct (S.b - 1)
  rw [hB.1, hPrev.1]
  simpa only [singleCornerCriticalStateAt_m] using hJump

/-- actual scanner 初期 state は semantic Hensel invariant を満たす。 -/
theorem singleCornerCertifiedStartState_correct
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedStartState R hL hCard).Correct := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let c := P.terminalCriticalStart
  let C := singleCornerCriticalStateAt c
  let A :=
    singleCornerInitialAffine
      (singleCornerCriticalStateAt S.b) S.width
  have hC := singleCornerCriticalStateAt_correct c
  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedStartState,
    P, S, c, C, A
  ] using SingleCornerHenselState.init_correct hC A

/-- actual scanner 初期 state の rank は corner 終端 `c`。 -/
theorem singleCornerCertifiedStartState_m
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedStartState R hL hCard).m =
      (M.toPureBProfileObstruction hL).terminalCriticalStart := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let c := P.terminalCriticalStart
  simp [
    MinimalActualABObstructionPacket.singleCornerCertifiedStartState,
    SingleCornerHenselState.init,
    singleCornerCriticalStateAt_m
  ]

/-- frozen state も semantic Hensel invariant を満たす。 -/
theorem singleCornerCertifiedFreezeState_correct
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFreezeState R hL hCard).Correct := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  have hStart :
      (M.singleCornerCertifiedStartState R hL hCard).Correct :=
    M.singleCornerCertifiedStartState_correct R hL hCard
  have h :=
    SingleCornerHenselState.iterate_correct
      (130 - c) hStart
  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedFreezeState,
    P, c
  ] using h

/-- frozen state の rank は `c + (130-c) = max(c,130)`。 -/
theorem singleCornerCertifiedFreezeState_m
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFreezeState R hL hCard).m =
      (M.toPureBProfileObstruction hL).terminalCriticalStart +
        (130 - (M.toPureBProfileObstruction hL).terminalCriticalStart) := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  have hStartM :
      (M.singleCornerCertifiedStartState R hL hCard).m = c := by
    simpa [P, c] using
      M.singleCornerCertifiedStartState_m R hL hCard
  have h :=
    SingleCornerHenselState.iterate_m
      (130 - c)
      (M.singleCornerCertifiedStartState R hL hCard)
  rw [hStartM] at h
  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedFreezeState,
    P, c
  ] using h

/--
chunked native certificate から actual candidate の短い prefix safety と
rank `max(c,130)` における 205-bit frozen residue certificate を読む。
-/
theorem singleCorner_certifiedFreezeCertificate
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (∀ j : ℕ,
      j <
          130 -
            (M.toPureBProfileObstruction hL).terminalCriticalStart →
        (SingleCornerHenselState.iterate j
          (M.singleCornerCertifiedStartState R hL hCard)).Safe) ∧
      SingleCornerHenselState.frozen205RepresentativeBound <
        (M.singleCornerCertifiedFreezeState R hL hCard).frozen205Residue := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let c := P.terminalCriticalStart
  let B := singleCornerCriticalStateAt S.b
  let C := singleCornerCriticalStateAt c
  let A := singleCornerInitialAffine B S.width
  let S0 := SingleCornerHenselState.init C A

  have hm2270 : P.m ≤ 2270 := by
    simpa [P] using M.singleCorner_card_one_m_le_2270 R hL hCard
  have hm6465 : P.m ≤ 6465 := by
    omega
  have hbLt : S.b < 116 := by
    simpa [P] using
      M.singleCorner_b_lt_116_of_m_le_6465 R hL S hm6465
  have hbPos : 0 < S.b :=
    S.b_pos
  have hWidth : S.width ≤ 213 := by
    simpa [P] using
      M.singleCorner_width_le_213_of_m_le_6465 R hL S hm6465
  have hWidthPos : 0 < S.width :=
    S.width_pos
  have hEntrance :=
    M.singleCorner_actual_henselEntrance hL S

  have hCheck :=
    singleCornerHenselCandidateFreezeCheck_of_bounds
      hbPos hbLt hWidthPos hWidth hEntrance

  have hcEq : S.b + S.width = c := by
    simpa [c] using S.b_add_width_eq_terminalStart
  rw [hcEq] at hCheck

  have hSound :=
    SingleCornerHenselState.scanToFreeze205_sound
      (130 - c) S0 hCheck

  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedStartState,
    MinimalActualABObstructionPacket.singleCornerCertifiedFreezeState,
    P, S, c, B, C, A, S0
  ] using hSound

/-- certified final state の affine numerator は actual profile affine numerator。 -/
theorem singleCorner_certifiedFinalState_A_eq_profile
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFinalState R hL hCard).A =
      profileAffineNumerator
        (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).h := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let c := P.terminalCriticalStart
  let B := singleCornerCriticalStateAt S.b
  let C := singleCornerCriticalStateAt c
  let A := singleCornerInitialAffine B S.width
  let S0 := SingleCornerHenselState.init C A

  have hC := singleCornerCriticalStateAt_correct c
  have hInitCorrect : S0.Correct := by
    simpa [S0, C] using SingleCornerHenselState.init_correct hC A
  have hInitM : S0.m = c := by
    change (singleCornerCriticalStateAt c).m = c
    exact singleCornerCriticalStateAt_m c
  have hA0 : A = profileAffineNumerator c P.h := by
    have h := S.profileAffineNumerator_terminalStart_eq_henselInitial
    simpa [A, B, c] using h.symm
  have hSuffix : IsTerminalCriticalSuffix P c :=
    P.terminalCriticalStart_spec
  have hcLeM : c ≤ P.m := hSuffix.1
  have hTrack :=
    henselIterate_A_eq_profileAffine
      hSuffix hInitCorrect hInitM hA0 (P.m - c)
      (by omega)
  have hEnd : c + (P.m - c) = P.m := by omega
  rw [hEnd] at hTrack
  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedFinalState,
    MinimalActualABObstructionPacket.singleCornerCertifiedStartState,
    P, S, c, B, C, A, S0
  ] using hTrack

/-- certified final state は semantic Hensel invariant を満たす。 -/
theorem singleCorner_certifiedFinalState_correct
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFinalState R hL hCard).Correct := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  have hInit :
      (M.singleCornerCertifiedStartState R hL hCard).Correct :=
    M.singleCornerCertifiedStartState_correct R hL hCard
  have hIter :=
    SingleCornerHenselState.iterate_correct (P.m - c) hInit
  simpa [
    MinimalActualABObstructionPacket.singleCornerCertifiedFinalState,
    P, c
  ] using hIter

/-- final state の rank は actual `m`。 -/
theorem singleCorner_certifiedFinalState_m
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFinalState R hL hCard).m =
      (M.toPureBProfileObstruction hL).m := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  have hcLeM : c ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hStartM :
      (M.singleCornerCertifiedStartState R hL hCard).m = c := by
    simpa [P, c] using
      M.singleCornerCertifiedStartState_m R hL hCard
  change
    (SingleCornerHenselState.iterate (P.m - c)
      (M.singleCornerCertifiedStartState R hL hCard)).m = P.m
  rw [SingleCornerHenselState.iterate_m, hStartM]
  omega

/-! ## 4. scanner representative = actual representative -/

/-- actual profile affine numerator は actual upper exponent-word affine constant。 -/
theorem singleCorner_profileAffine_eq_actualWordAffine
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    profileAffineNumerator P.m P.h =
      Collatz2.Word.affineConst M.actual.firstFailureEdge.upperExponentWord := by
  let P := M.toPureBProfileObstruction hL
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hProfile :=
    firstPassage_profileAffineNumerator_eq_wordAffineConst
      M.word_firstPassage hLen
  have hmOdd :
      P.m = Collatz2.Word.oddSteps (exponentWordOfParity M.word) := by
    have hm := M.toPureBProfileObstruction_m_eq_wordOddCount hL
    rw [oddSteps_exponentWordOfParity]
    exact hm
  have hh : P.h = parityExtraDepth M.word := by
    funext k
    exact M.toPureBProfileObstruction_h_apply hL k
  rw [← hmOdd, ← hh] at hProfile
  rw [← M.actualUpperExponentWord_eq_exponentWordOfParity] at hProfile
  simpa [P] using hProfile

/-- actual upper exponent word の total two-depth は `beta_m+1`。 -/
theorem singleCorner_actual_twoSteps_eq_beta_add_one
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    Collatz2.Word.twoSteps M.actual.firstFailureEdge.upperExponentWord =
      beattyIndex (M.toPureBProfileObstruction hL).m + 1 := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have h :=
    firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one
      M.word_firstPassage hLen
  rw [← M.actualUpperExponentWord_eq_exponentWordOfParity] at h
  have hmW := M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  rw [hmW] at h
  exact h

/-- actual edge modulus は scanner final modulus と同じ。 -/
theorem singleCorner_actual_edge_modulus_eq
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    M.actual.firstFailureEdge.step.edge.modulus =
      2 ^ (beattyIndex (M.toPureBProfileObstruction hL).m + 1) := by
  let F := M.actual.firstFailureEdge
  have hUpper : F.step.edge.upperWord = M.word := by
    simpa [F] using M.actualFirstFailureUpperWord_eq_word
  have hLen : M.word.length = beattyIndex (M.toPureBProfileObstruction hL).m + 1 := by
    have hTwo := M.singleCorner_actual_twoSteps_eq_beta_add_one hL
    rw [M.actualUpperExponentWord_eq_exponentWordOfParity] at hTwo
    have hTL := M.word_firstPassage.twoSteps_exponentWordOfParity_eq_length (by
      rw [M.word_length_eq]
      omega)
    rw [hTL] at hTwo
    exact hTwo
  unfold AdjacentFerrersSwap.modulus
  rw [← F.step.edge.upperWord_length, hUpper, hLen]

/-- scanner final representative は actual first-failure upper representative と一致。 -/
theorem singleCorner_certifiedFinalState_R_eq_upperR
    (Rhin : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFinalState Rhin hL hCard).R =
      M.actual.firstFailureEdge.step.edge.upperR := by
  let P := M.toPureBProfileObstruction hL
  let T := M.singleCornerCertifiedFinalState Rhin hL hCard
  let F := M.actual.firstFailureEdge
  have hTCorrect : T.Correct := by
    simpa [T] using M.singleCorner_certifiedFinalState_correct Rhin hL hCard
  have hTm : T.m = P.m := by
    simpa [T, P] using M.singleCorner_certifiedFinalState_m Rhin hL hCard
  have hTA : T.A = profileAffineNumerator P.m P.h := by
    simpa [T, P] using M.singleCorner_certifiedFinalState_A_eq_profile Rhin hL hCard
  have hProfileActual :
      profileAffineNumerator P.m P.h = Collatz2.Word.affineConst F.upperExponentWord := by
    simpa [P, F] using M.singleCorner_profileAffine_eq_actualWordAffine hL
  have hOdd : Collatz2.Word.oddSteps F.upperExponentWord = P.m := by
    simpa [F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hTwo : Collatz2.Word.twoSteps F.upperExponentWord = beattyIndex P.m + 1 := by
    simpa [F, P] using M.singleCorner_actual_twoSteps_eq_beta_add_one hL
  have hReal := FirstFailureEdge.upperExponentWord_realizesCanonical F
  rw [Collatz2.Word.realizes_iff] at hReal
  have hActualEq :
      3 ^ P.m * F.step.edge.upperR + profileAffineNumerator P.m P.h =
        2 ^ (beattyIndex P.m + 1) *
          (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [hOdd, hTwo, hProfileActual, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hReal.symm

  have hScanEq :
      3 ^ P.m * T.R + profileAffineNumerator P.m P.h =
        2 ^ (beattyIndex P.m + 1) * T.q := by
    have hEq := hTCorrect.2.2.1
    unfold SingleCornerHenselState.modulus at hEq
    rw [hTCorrect.1, hTm, hTCorrect.2.1, hTm, hTA] at hEq
    exact hEq

  have hRScan : T.R < 2 ^ (beattyIndex P.m + 1) := by
    have h := hTCorrect.2.2.2
    unfold SingleCornerHenselState.modulus at h
    rw [hTCorrect.1, hTm] at h
    exact h
  have hRActual :
      F.step.edge.upperR < 2 ^ (beattyIndex P.m + 1) := by
    have h := F.step.edge.upperR_lt_modulus
    rw [M.singleCorner_actual_edge_modulus_eq hL] at h
    simpa [P, F] using h

  exact
    twoPowerAffineRepresentative_unique
      hScanEq hActualEq hRScan hRActual


/--
native certificate から actual final state の safety を得る。

`m < 130` なら rank 130 までの短い scan から直接読む。
`130 ≤ m` なら 205-bit residue は freeze point から final state まで不変であり、
その residue は `rhinGapK * 2271^15` より大きい。一方 actual representative は
既存 Rhin bound で同じ値以下なので矛盾する。
-/
theorem singleCorner_certifiedFinalState_safe
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.singleCornerCertifiedFinalState R hL hCard).Safe := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let S0 := M.singleCornerCertifiedStartState R hL hCard
  let Z := M.singleCornerCertifiedFreezeState R hL hCard
  let T := M.singleCornerCertifiedFinalState R hL hCard
  let F := M.actual.firstFailureEdge

  have hm2270 : P.m ≤ 2270 := by
    simpa [P] using
      M.singleCorner_card_one_m_le_2270 R hL hCard
  have hcLeM : c ≤ P.m :=
    P.terminalCriticalStart_spec.1

  have hCert :=
    M.singleCorner_certifiedFreezeCertificate R hL hCard

  by_cases hm130 : P.m < 130
  · have hOffset :
        P.m - c < 130 - c := by
      omega
    have hSafe :=
      hCert.1 (P.m - c) (by simpa [P, c] using hOffset)
    simpa [
      T,
      MinimalActualABObstructionPacket.singleCornerCertifiedFinalState,
      P, c, S0
    ] using hSafe

  · have hm130' : 130 ≤ P.m := by
      omega

    have hFreezeCorrect : Z.Correct := by
      simpa [Z] using
        M.singleCornerCertifiedFreezeState_correct R hL hCard

    have hFreezeM :
        Z.m = c + (130 - c) := by
      simpa [Z, P, c] using
        M.singleCornerCertifiedFreezeState_m R hL hCard

    have hmFreeze : 130 ≤ Z.m := by
      rw [hFreezeM]
      omega

    have hBetaFreeze : 205 ≤ Z.beta :=
      SingleCornerHenselState.beta_ge_205_of_correct_m_ge_130
        hFreezeCorrect hmFreeze

    have hFreezeLe :
        130 - c ≤ P.m - c := by
      omega
    obtain ⟨d, hTotal⟩ :=
      Nat.exists_eq_add_of_le hFreezeLe

    have hTFromFreeze :
        T = SingleCornerHenselState.iterate d Z := by
      change
        SingleCornerHenselState.iterate (P.m - c) S0 =
          SingleCornerHenselState.iterate d
            (SingleCornerHenselState.iterate (130 - c) S0)
      rw [hTotal, SingleCornerHenselState.iterate_add]

    have hResidueTail :=
      SingleCornerHenselState.iterate_frozen205Residue_eq
        d (S := Z) hBetaFreeze

    have hFinalResidue :
        T.frozen205Residue = Z.frozen205Residue := by
      rw [hTFromFreeze]
      exact hResidueTail

    have hFreezeBound :
        SingleCornerHenselState.frozen205RepresentativeBound <
          Z.frozen205Residue := by
      simpa [Z] using hCert.2

    have hFinalBound :
        SingleCornerHenselState.frozen205RepresentativeBound <
          T.frozen205Residue := by
      rw [hFinalResidue]
      exact hFreezeBound

    have hR :
        T.R = F.step.edge.upperR := by
      simpa [T, F] using
        M.singleCorner_certifiedFinalState_R_eq_upperR R hL hCard

    have hRPoly :=
      M.actualRepresentative_le_rhinPolynomial R hL

    have hm1 : P.m + 1 ≤ 2271 := by
      omega

    have hPow :
        (P.m + 1) ^ 15 ≤ 2271 ^ 15 :=
      Nat.pow_le_pow_left hm1 15

    have hRBound :
        F.step.edge.upperR ≤
          SingleCornerHenselState.frozen205RepresentativeBound := by
      unfold SingleCornerHenselState.frozen205RepresentativeBound
      exact
        le_trans
          (by simpa [P, F] using hRPoly)
          (Nat.mul_le_mul_left rhinGapK hPow)

    have hTLt205 : T.R < 2 ^ 205 := by
      rw [hR]
      exact
        lt_of_le_of_lt hRBound
          SingleCornerHenselState.frozen205RepresentativeBound_lt_pow205

    have hTResidue :
        T.frozen205Residue = T.R := by
      unfold SingleCornerHenselState.frozen205Residue
      exact Nat.mod_eq_of_lt hTLt205

    rw [hTResidue, hR] at hFinalBound
    omega

/-! ## 5. complete card-one closure -/

/--
actual minimal B obstruction の single exposed corner branch は不可能。

この theorem で `card = 1` finite residue は完全に消える。
-/
theorem singleCorner_card_one_impossible
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    False := by
  let P := M.toPureBProfileObstruction hL
  let T := M.singleCornerCertifiedFinalState R hL hCard
  let F := M.actual.firstFailureEdge

  have hSafe : T.Safe := by
    simpa [T] using M.singleCorner_certifiedFinalState_safe R hL hCard
  have hR : T.R = F.step.edge.upperR := by
    simpa [T, F] using M.singleCorner_certifiedFinalState_R_eq_upperR R hL hCard
  have hTCorrect : T.Correct := by
    simpa [T] using M.singleCorner_certifiedFinalState_correct R hL hCard
  have hTm : T.m = P.m := by
    simpa [T, P] using M.singleCorner_certifiedFinalState_m R hL hCard
  have hTA : T.A = profileAffineNumerator P.m P.h := by
    simpa [T, P] using M.singleCorner_certifiedFinalState_A_eq_profile R hL hCard
  have hProfileActual :
      profileAffineNumerator P.m P.h = Collatz2.Word.affineConst F.upperExponentWord := by
    simpa [P, F] using M.singleCorner_profileAffine_eq_actualWordAffine hL
  have hOdd : Collatz2.Word.oddSteps F.upperExponentWord = P.m := by
    simpa [F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hTwo : Collatz2.Word.twoSteps F.upperExponentWord = beattyIndex P.m + 1 := by
    simpa [F, P] using M.singleCorner_actual_twoSteps_eq_beta_add_one hL

  have hScanEq :
      3 ^ P.m * T.R + profileAffineNumerator P.m P.h =
        2 ^ (beattyIndex P.m + 1) * T.q := by
    have hEq := hTCorrect.2.2.1
    unfold SingleCornerHenselState.modulus at hEq
    rw [hTCorrect.1, hTm, hTCorrect.2.1, hTm, hTA] at hEq
    exact hEq

  have hReal := FirstFailureEdge.upperExponentWord_realizesCanonical F
  rw [Collatz2.Word.realizes_iff] at hReal
  have hActualEq :
      3 ^ P.m * F.step.edge.upperR + profileAffineNumerator P.m P.h =
        2 ^ (beattyIndex P.m + 1) *
          (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [hOdd, hTwo, hProfileActual, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hReal.symm

  rw [← hR] at hActualEq
  have hQ : T.q = T.R + F.upperNormalizedDefectNat := by
    have hPowPos : 0 < 2 ^ (beattyIndex P.m + 1) := by
      positivity
    have hEqMul :
        2 ^ (beattyIndex P.m + 1) * T.q =
          2 ^ (beattyIndex P.m + 1) *
            (T.R + F.upperNormalizedDefectNat) := by
      calc
        2 ^ (beattyIndex P.m + 1) * T.q
            =
          3 ^ P.m * T.R +
            profileAffineNumerator P.m P.h := hScanEq.symm
        _ =
          2 ^ (beattyIndex P.m + 1) *
            (T.R + F.upperNormalizedDefectNat) := hActualEq
    exact Nat.mul_left_cancel hPowPos hEqMul
  unfold SingleCornerHenselState.Safe at hSafe
  rw [hQ] at hSafe
  omega

/--
actual minimal B obstruction では exposed predecessor は nonempty なので、
card-one elimination 後は必ず二個以上。
-/
theorem exposedPredecessorSet_card_ge_two
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    2 ≤ (M.toPureBProfileObstruction hL).exposedPredecessorSet.card := by
  have hNonempty := M.exposedPredecessorSet_nonempty R hL
  have hPos :
      0 < (M.toPureBProfileObstruction hL).exposedPredecessorSet.card :=
    Finset.card_pos.mpr hNonempty
  by_contra hnot
  have hOne :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1 := by
    omega
  exact M.singleCorner_card_one_impossible R hL hOne

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
