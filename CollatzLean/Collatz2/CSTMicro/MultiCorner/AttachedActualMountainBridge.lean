import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRightEndSmallness
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalizationUnitBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerCriticalizationRun

/-!
# MultiCorner attached branch: actual straight mountain bridge

`7362ed058f7345f2b4cd799b3f115c8750bd0647` で公開された
actual interval transport を attached straight corridor に移植する。

このファイルの目的は、これまで別々に存在した

* actual odd-only prefix state `X_k`,
* integral critical state `Z_k`,
* free-base Hensel shifted state `Q_k = q_k + 1`,
* fused state `S_k = 2^(h_k) Z_k + Q_k`,

を terminal mountain 上で exact に同一座標へ戻すことである。

主要結論は次の八本。

1. `actualStraightRun_eq_replicate_one`
2. `actualStraightShiftTransport`
3. `terminalCriticalState_scaled_eq_actualPrefixState`
4. `terminalPred_fused_eq_actualShiftedState`
5. `straightFused_eq_actualShiftedState`
6. `exists_terminalMountainCofactor`
7. `terminalCarryRhs_eq_two_mul_threePow_mul_mountainCofactor`
8. `terminalNearAnchorBudgetV_impossible`

最後の theorem は旧 right-end-smallness route の第一 anchor budget が
actual positive attached branch と両立しないことを明示する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-! ## 0. actual upper exponent word の canonical prefix state -/

namespace MinimalActualABObstructionPacket

/--
actual first-failure upper exponent word の rank `k` における canonical odd-prefix state。

`realizedPrefixState` の proof argument を後段から隠すための薄い wrapper。
-/
noncomputable def actualUpperPrefixState
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (k : ℕ)
    (hk : k ≤ (M.toPureBProfileObstruction hL).m) : ℕ := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  have hReal :
      Collatz2.Word.Realizes F.upperExponentWord
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    exact FirstFailureEdge.upperExponentWord_realizesCanonical F
  have hOdd :
      Collatz2.Word.oddSteps F.upperExponentWord = P.m := by
    simpa [P, F] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hkW : k ≤ Collatz2.Word.oddSteps F.upperExponentWord := by
    rw [hOdd]
    exact hk
  exact realizedPrefixState hReal k hkW

/-- canonical actual prefix state の raw affine specification。 -/
theorem actualUpperPrefixState_spec
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k ≤ (M.toPureBProfileObstruction hL).m) :
    let F := M.actual.firstFailureEdge
    3 ^ k * F.step.edge.upperR +
        Collatz2.Word.affineConst (F.upperExponentWord.take k) =
      2 ^ Collatz2.Word.prefixTwoDepth F.upperExponentWord k *
        actualUpperPrefixState M hL k hk := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  have hReal :
      Collatz2.Word.Realizes F.upperExponentWord
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    exact FirstFailureEdge.upperExponentWord_realizesCanonical F
  have hOdd :
      Collatz2.Word.oddSteps F.upperExponentWord = P.m := by
    simpa [P, F] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hkW : k ≤ Collatz2.Word.oddSteps F.upperExponentWord := by
    rw [hOdd]
    exact hk
  have h := realizedPrefixState_spec hReal k hkW
  simpa [actualUpperPrefixState, P, F, Collatz2.Word.prefixTwoDepth] using h

/--
actual upper word の `k`-prefix affine constant は pure profile の
`k`-prefix affine numerator と exact に一致する。
-/
private theorem actualUpperTake_affineConst_eq_profile
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k ≤ (M.toPureBProfileObstruction hL).m) :
    let P := M.toPureBProfileObstruction hL
    let F := M.actual.firstFailureEdge
    Collatz2.Word.affineConst (F.upperExponentWord.take k) =
      profileAffineNumerator k P.h := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  have hOdd : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using
      M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hLen : w.length = P.m := by
    simpa [Collatz2.Word.oddSteps] using hOdd
  have hkLen : k ≤ w.length := by
    rw [hLen]
    exact hk
  have hTakeOdd : Collatz2.Word.oddSteps (w.take k) = k := by
    dsimp [Collatz2.Word.oddSteps]
    exact List.length_take_of_le hkLen
  have hProfile :=
    profileAffineNumerator_eq_affineConst_of_checkpoint
      (m := k) (h := P.h) (w := w.take k)
      hTakeOdd.symm
      (by
        intro j hj
        have hjM : j < P.m := lt_of_lt_of_le hj hk
        have hCoord := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hjM
        have hTake :
            Collatz2.Word.prefixTwoDepth (w.take k) j =
              Collatz2.Word.prefixTwoDepth w j := by
          unfold Collatz2.Word.prefixTwoDepth
          rw [List.take_take]
          rw [min_eq_left (Nat.le_of_lt hj)]
        rw [hTake]
        simpa [w, F, P] using hCoord.symm)
  exact hProfile.symm

/-- actual prefix state を profile affine numerator で読む。 -/
theorem actualUpperPrefixState_profile_spec
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k ≤ (M.toPureBProfileObstruction hL).m) :
    let P := M.toPureBProfileObstruction hL
    let F := M.actual.firstFailureEdge
    3 ^ k * F.step.edge.upperR +
        profileAffineNumerator k P.h =
      2 ^ Collatz2.Word.prefixTwoDepth F.upperExponentWord k *
        actualUpperPrefixState M hL k hk := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  have hRaw := MinimalActualABObstructionPacket.actualUpperPrefixState_spec M hL hk
  have hAffine := MinimalActualABObstructionPacket.actualUpperTake_affineConst_eq_profile M hL hk
  dsimp [P, F] at hRaw hAffine ⊢
  rw [hAffine] at hRaw
  exact hRaw

end MinimalActualABObstructionPacket

/-!
profile affine numerator の one-cell recurrence。

terminal critical/noncritical の別を使わない pure finite-sum identity。
-/
private theorem profileAffineNumerator_succ_general
    (h : ℕ → ℕ)
    (r : ℕ) :
    profileAffineNumerator (r + 1) h =
      3 * profileAffineNumerator r h +
        2 ^ profileCheckpoint h r := by
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
    have hExp :
        r + 1 - (k + 1) = (r - (k + 1)) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLast : r + 1 - (r + 1) = 0 := by omega
  rw [hLast, pow_zero, mul_one]

namespace AttachedTwoCornerPacket

/-- occupied straight index は actual odd range の strict interior にある。 -/
private theorem straight_index_lt_profile_m
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    A.straightHenselStart + i < P.m := by
  have hEnd := A.straightHenselStart_add_width
  have hcM := P.terminalCriticalStart_spec.1
  omega

/-- straight suffix の最後の occupied rank は terminal predecessor。 -/
private theorem straight_last_eq_terminal
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.straightHenselStart + (A.straightHenselWidth - 1) =
      A.normalForm.terminal := by
  have hW := A.straightHenselWidth_pos
  have hEnd := A.straightHenselStart_add_width
  have hSucc := A.terminal_succ_eq_terminalCriticalStart
  omega

/-! ## 1. actual straight run = all-one exponent block -/

/--
attached straight corridor の任意 subinterval は actual exponent word 上でも
exact に `[1,...,1]`。
-/
theorem actualStraightRun_eq_replicate_one
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i r : ℕ}
    (hEnd : i + r < A.straightHenselWidth) :
    let F := M.actual.firstFailureEdge
    let b := A.straightHenselStart + i
    (F.upperExponentWord.drop b).take r =
      List.replicate r 1 := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let b := A.straightHenselStart + i
  let t : Collatz2.Word := (w.drop b).take r
  have hi : i < A.straightHenselWidth := by omega
  have hiR : i + r < A.straightHenselWidth := hEnd
  have hbM : b < P.m := by
    dsimp [b]
    exact A.straight_index_lt_profile_m hi
  have hbrM : b + r < P.m := by
    dsimp [b]
    have h := A.straight_index_lt_profile_m hiR
    simpa [Nat.add_assoc] using h
  have hLineB := A.straight_profileCheckpoint_eq_base_add hi
  have hLineE := A.straight_profileCheckpoint_eq_base_add hiR
  have hDepthB0 := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hbM
  have hDepthE0 := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hbrM
  have hDepthB :
      Collatz2.Word.prefixTwoDepth w b =
        profileCheckpoint P.h A.straightHenselStart + i := by
    dsimp [w, F, P, b] at hDepthB0 ⊢
    rw [hDepthB0]
    exact hLineB
  have hDepthE :
      Collatz2.Word.prefixTwoDepth w (b + r) =
        profileCheckpoint P.h A.straightHenselStart + (i + r) := by
    have hIdx :
        A.straightHenselStart + i + r =
          A.straightHenselStart + (i + r) := by omega
    dsimp [w, F, P, b] at hDepthE0 ⊢
    rw [hDepthE0, hIdx]
    exact hLineE
  have hTakeAdd :
      w.take (b + r) = w.take b ++ t := by
    dsimp [t]
    simpa using
      (List.take_add :
        w.take (b + r) =
          w.take b ++ (w.drop b).take r)
  have hTwoT : Collatz2.Word.twoSteps t = r := by
    have hSum :
        Collatz2.Word.twoSteps (w.take (b + r)) =
          Collatz2.Word.twoSteps (w.take b) +
            Collatz2.Word.twoSteps t := by
      rw [hTakeAdd, Collatz2.Word.twoSteps_append]
    change
      Collatz2.Word.twoSteps (w.take b) =
        profileCheckpoint P.h A.straightHenselStart + i at hDepthB
    change
      Collatz2.Word.twoSteps (w.take (b + r)) =
        profileCheckpoint P.h A.straightHenselStart + (i + r) at hDepthE
    omega
  have hOddW : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hrDrop : r ≤ (w.drop b).length := by
    rw [List.length_drop]
    have hwLen : w.length = P.m := by
      simpa [Collatz2.Word.oddSteps] using hOddW
    rw [hwLen]
    omega
  have hOddT : Collatz2.Word.oddSteps t = r := by
    dsimp [t, Collatz2.Word.oddSteps]
    exact List.length_take_of_le hrDrop
  have hValidW : Collatz2.Word.Valid w := by
    simpa [w] using F.upperExponentWord_valid
  have hDropValid : Collatz2.Word.Valid (w.drop b) := by
    have hWhole :
        Collatz2.Word.Valid (w.take b ++ w.drop b) := by
      simpa using hValidW
    exact hWhole.suffix
  have hValidT : Collatz2.Word.Valid t := by
    have hWhole :
        Collatz2.Word.Valid
          ((w.drop b).take r ++ (w.drop b).drop r) := by
      simpa [t] using hDropValid
    exact hWhole.prefix
  have hEq :
      Collatz2.Word.twoSteps t = Collatz2.Word.oddSteps t := by
    rw [hTwoT, hOddT]
  have hRun :=
    word_eq_replicate_one_of_valid_twoSteps_eq_oddSteps
      t hValidT hEq
  simpa [t, hOddT] using hRun

/-! ## 2. actual shifted state の homogeneous transport -/

/--
actual straight corridor では shifted state `X+1` が fused state と同じ
`3/2` homogeneous transport を満たす。
-/
theorem actualStraightShiftTransport
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i r : ℕ}
    (hEnd : i + r < A.straightHenselWidth) :
    let b := A.straightHenselStart + i
    2 ^ r *
        (MinimalActualABObstructionPacket.actualUpperPrefixState M hL (b + r)
            (Nat.le_of_lt (by
              dsimp [b]
              simpa [Nat.add_assoc] using
                (A.straight_index_lt_profile_m (i := i + r) hEnd))) + 1) =
      3 ^ r *
        (MinimalActualABObstructionPacket.actualUpperPrefixState M hL b
            (Nat.le_of_lt (by
              dsimp [b]
              exact A.straight_index_lt_profile_m (by omega))) + 1) := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let b := A.straightHenselStart + i
  have hi : i < A.straightHenselWidth := by omega
  have hbM : b < P.m := by
    dsimp [b]
    exact A.straight_index_lt_profile_m hi
  have hbrM : b + r < P.m := by
    dsimp [b]
    have h := A.straight_index_lt_profile_m hEnd
    simpa [Nat.add_assoc] using h
  have hOdd : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hbW : b ≤ Collatz2.Word.oddSteps w := by
    rw [hOdd]
    omega
  have hbrW : b + r ≤ Collatz2.Word.oddSteps w := by
    rw [hOdd]
    omega
  have hReal :
      Collatz2.Word.Realizes w
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [w] using FirstFailureEdge.upperExponentWord_realizesCanonical F
  have hRun := A.actualStraightRun_eq_replicate_one M hL hEnd
  have hShift :=
    oneRun_exact_shift_transport
      (w := w)
      (x := F.step.edge.upperR)
      (y := F.step.edge.upperR + F.upperNormalizedDefectNat)
      (b := b) (r := r)
      hReal hbW hbrW
      (by simpa [w, F, b] using hRun)
  simpa [
    MinimalActualABObstructionPacket.actualUpperPrefixState,
    P, F, w, b
  ] using hShift

/-! ## 3. terminal integral critical state = scaled actual prefix state -/

/--
terminal critical start `c` の integral critical state と actual prefix state は、
それぞれの natural dyadic checkpoint で scale すると exact に一致する。

`c=m` の場合だけ actual total depth に final `+1` があるため、
この theorem は無理に `Z_c=X_c` とせず scale を保った形で述べる。
-/
theorem terminalCriticalState_scaled_eq_actualPrefixState
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    let F := M.actual.firstFailureEdge
    let c := P.terminalCriticalStart
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I c
        P.criticalizationStart_le_terminalCriticalStart
        P.terminalCriticalStart_spec.1
    let X :=
      MinimalActualABObstructionPacket.actualUpperPrefixState M hL c P.terminalCriticalStart_spec.1
    (2 : ℤ) ^ beattyIndex c * Z =
      (2 : ℤ) ^ Collatz2.Word.prefixTwoDepth F.upperExponentWord c *
        (X : ℤ) := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let c := P.terminalCriticalStart
  let I := P.criticalizationStart_spec
  let Z :=
    P.integralCriticalTailStateInt
      I c
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  let X :=
    MinimalActualABObstructionPacket.actualUpperPrefixState M hL c P.terminalCriticalStart_spec.1
  have hState :=
    P.terminalCritical_integralState_scaled_eq_localPrefix_add_y_sub_q
  have hLocal :=
    profileAffineLocalPrefixZ_eq_profileAffineNumerator_cast_terminal P
  have hY := M.toPureBProfileObstruction_y_sub_q_eq_leastRepresentative hL
  have hUpper : F.step.edge.upperWord = M.word := by
    simpa [F] using M.actualFirstFailureUpperWord_eq_word
  have hR : F.step.edge.upperR = leastRepresentative M.word := by
    unfold AdjacentFerrersSwap.upperR
    rw [hUpper]
  have hActualNat :=
    MinimalActualABObstructionPacket.actualUpperPrefixState_profile_spec
      M hL P.terminalCriticalStart_spec.1
  have hActual := congrArg (fun n : ℕ => (n : ℤ)) hActualNat
  push_cast at hActual
  dsimp [P, F, c, X] at hActual
  rw [hR] at hActual
  dsimp [P, c, I, Z] at hState hLocal hY ⊢
  rw [hLocal, hY] at hState
  have hActual' :
      (2 : ℤ) ^ Collatz2.Word.prefixTwoDepth F.upperExponentWord P.terminalCriticalStart *
          (MinimalActualABObstructionPacket.actualUpperPrefixState M hL P.terminalCriticalStart
            P.terminalCriticalStart_spec.1 : ℤ) =
        (profileAffineNumerator P.terminalCriticalStart P.h : ℤ) +
          (3 : ℤ) ^ P.terminalCriticalStart *
            (leastRepresentative M.word : ℤ) := by
    linarith [hActual]
  rw [hState]
  exact hActual'.symm

/-! ## 4. terminal predecessor fused state = actual shifted state -/

/--
terminal predecessor では fused state は actual odd state `X_k+1` そのもの。

proof は terminal carry RHS の prefix-side identityと actual prefix affine equationを
同じ `2^p` scale で比較し、最後に dyadic factor を cancel する。
-/
theorem terminalPred_fused_eq_actualShiftedState
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart : 0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    let k := A.normalForm.terminal
    A.straightCriticalFusedState hStart (A.straightHenselWidth - 1) =
      (MinimalActualABObstructionPacket.actualUpperPrefixState M hL k
          (Nat.le_of_lt A.terminal_isExposed.lt_m) : ℤ) + 1 := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let k := A.normalForm.terminal
  let c := P.terminalCriticalStart
  let p := P.terminalTopCellPosition
  let X :=
    MinimalActualABObstructionPacket.actualUpperPrefixState
      M hL k (Nat.le_of_lt A.terminal_isExposed.lt_m)
  have hkM : k < P.m := A.terminal_isExposed.lt_m
  have hSucc : k + 1 = c := by
    dsimp [k, c]
    exact A.terminal_succ_eq_terminalCriticalStart
  have hTop : p = profileCheckpoint P.h k := by
    dsimp [p, k]
    exact A.terminalTopCellPosition_eq_terminal_checkpoint
  have hCoord0 := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hkM
  have hDepth :
      Collatz2.Word.prefixTwoDepth F.upperExponentWord k = p := by
    dsimp [F, P, k, p] at hCoord0 ⊢
    rw [hCoord0]
    exact A.terminalTopCellPosition_eq_terminal_checkpoint.symm
  have hActualNat :=
    MinimalActualABObstructionPacket.actualUpperPrefixState_profile_spec M hL (Nat.le_of_lt hkM)
  have hActual := congrArg (fun n : ℕ => (n : ℤ)) hActualNat
  push_cast at hActual
  dsimp [P, F, k, X] at hActual
  rw [hDepth] at hActual
  have hRecNat := profileAffineNumerator_succ_general P.h k
  have hRec := congrArg (fun n : ℕ => (n : ℤ)) hRecNat
  push_cast at hRec
  rw [← hTop] at hRec
  have hCarry := A.terminalCarryRhs_scaled_eq_localPrefix_add_y_sub_q
  have hLocal :=
    profileAffineLocalPrefixZ_eq_profileAffineNumerator_cast_terminal P
  have hY0 := M.toPureBProfileObstruction_y_sub_q_eq_leastRepresentative hL
  have hUpper : F.step.edge.upperWord = M.word := by
    simpa [F] using M.actualFirstFailureUpperWord_eq_word
  have hR : F.step.edge.upperR = leastRepresentative M.word := by
    unfold AdjacentFerrersSwap.upperR
    rw [hUpper]
  have hY : P.y - (P.q : ℤ) = (F.step.edge.upperR : ℤ) := by
    rw [hY0]
    exact_mod_cast hR.symm
  have hScaled :
      (2 : ℤ) ^ p * A.terminalCarryRhs =
        (2 : ℤ) ^ p * (3 * ((X : ℤ) + 1)) := by
    calc
      (2 : ℤ) ^ p * A.terminalCarryRhs
          = P.profileAffineLocalPrefixZ c +
              (3 : ℤ) ^ c * (P.y - (P.q : ℤ)) +
              (2 : ℤ) ^ (p + 1) := by
            simpa [P, c, p] using hCarry
      _ =
          (profileAffineNumerator c P.h : ℤ) +
              (3 : ℤ) ^ c * (F.step.edge.upperR : ℤ) +
              (2 : ℤ) ^ (p + 1) := by
            rw [hLocal, hY]
      _ =
          (3 * (profileAffineNumerator k P.h : ℤ) + (2 : ℤ) ^ p) +
              (3 : ℤ) ^ (k + 1) * (F.step.edge.upperR : ℤ) +
              (2 : ℤ) ^ (p + 1) := by
            rw [← hSucc]
            rw [hRec]
      _ =
          3 *
              ((3 : ℤ) ^ k * (F.step.edge.upperR : ℤ) +
                (profileAffineNumerator k P.h : ℤ)) +
            3 * (2 : ℤ) ^ p := by
              rw [pow_succ, pow_succ]
              ring
      _ =
          3 * ((2 : ℤ) ^ p * (X : ℤ)) +
            3 * (2 : ℤ) ^ p := by
              rw [hActual]
      _ = (2 : ℤ) ^ p * (3 * ((X : ℤ) + 1)) := by
            ring
  have hPowNe : (2 : ℤ) ^ p ≠ 0 := by positivity
  have hE : A.terminalCarryRhs = 3 * ((X : ℤ) + 1) :=
    mul_left_cancel₀ hPowNe hScaled
  have hAnchor := A.straightCriticalFusedState_terminalPred_anchor hStart
  have hThreeNe : (3 : ℤ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ hThreeNe
  calc
    3 * A.straightCriticalFusedState hStart (A.straightHenselWidth - 1)
        = A.terminalCarryRhs := hAnchor
    _ = 3 * ((X : ℤ) + 1) := hE

/-! ## 5. corridor 全体で fused state = actual shifted state -/

/--
terminal predecessor の一致を同じ homogeneous transport で左へ戻すと、
straight corridor の全 occupied index で

  S_i = X_(s+i) + 1

が exact に成り立つ。
-/
theorem straightFused_eq_actualShiftedState
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart : 0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let k := A.straightHenselStart + i
    A.straightCriticalFusedState hStart i =
      (MinimalActualABObstructionPacket.actualUpperPrefixState M hL k
          (Nat.le_of_lt (A.straight_index_lt_profile_m hi)) : ℤ) + 1 := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  let d := A.straightHenselWidth - 1 - i
  let k := A.straightHenselStart + i
  let X :=
    MinimalActualABObstructionPacket.actualUpperPrefixState M hL k
      (Nat.le_of_lt (A.straight_index_lt_profile_m hi))
  have hW := A.straightHenselWidth_pos
  have hIdx : i + d = A.straightHenselWidth - 1 := by
    dsimp [d]
    omega
  have hEnd : i + d < A.straightHenselWidth := by
    rw [hIdx]
    omega
  have hFused := A.straightCriticalFusedState_transport hStart hEnd
  rw [hIdx] at hFused
  have hLast := A.terminalPred_fused_eq_actualShiftedState M hL hStart
  have hPredIdx := A.straight_last_eq_terminal
  have hActualNat :=
    A.actualStraightShiftTransport M hL (i := i) (r := d) hEnd
  have hActual := congrArg (fun n : ℕ => (n : ℤ)) hActualNat
  push_cast at hActual
  have hActualEndIdx :
      A.straightHenselStart + i + d =
        A.normalForm.terminal := by
    calc
      A.straightHenselStart + i + d
          = A.straightHenselStart + (i + d) := by
              simp [Nat.add_assoc]
      _ = A.straightHenselStart +
            (A.straightHenselWidth - 1) := by
              rw [hIdx]
      _ = A.normalForm.terminal := hPredIdx
  have hActual' :
      (2 : ℤ) ^ d *
          ((MinimalActualABObstructionPacket.actualUpperPrefixState M hL
              A.normalForm.terminal
              (Nat.le_of_lt A.terminal_isExposed.lt_m) : ℤ) + 1) =
        (3 : ℤ) ^ d * ((X : ℤ) + 1) := by
    dsimp [P, k, X] at hActual ⊢
    simpa [Nat.add_assoc, hActualEndIdx] using hActual
  have hScaled :
      (3 : ℤ) ^ d * A.straightCriticalFusedState hStart i =
        (3 : ℤ) ^ d * ((X : ℤ) + 1) := by
    calc
      (3 : ℤ) ^ d * A.straightCriticalFusedState hStart i
          = (2 : ℤ) ^ d *
              A.straightCriticalFusedState
                hStart (A.straightHenselWidth - 1) := hFused
      _ = (2 : ℤ) ^ d *
              ((MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
                  (Nat.le_of_lt A.terminal_isExposed.lt_m) : ℤ) + 1) := by
            rw [hLast]
      _ = (3 : ℤ) ^ d * ((X : ℤ) + 1) := hActual'
  have hPowNe : (3 : ℤ) ^ d ≠ 0 := by positivity
  exact mul_left_cancel₀ hPowNe hScaled

/-! ## 6. actual terminal mountain cofactor -/

/-- terminal carry RHS は even。 -/
private theorem terminalCarryRhs_even
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    (2 : ℤ) ∣ A.terminalCarryRhs := by
  let c := P.terminalCriticalStart
  let I := P.criticalizationStart_spec
  let e := carryRunGap P c A.normalForm.terminal
  let Z :=
    P.integralCriticalTailStateInt
      I c
      P.criticalizationStart_le_terminalCriticalStart
      P.terminalCriticalStart_spec.1
  have he : 1 ≤ e := by
    dsimp [e, c]
    have h := A.two_le_terminal_carryRunGap
    omega
  have hExp :
      e = (e - 1) + 1 := by
    omega
  have hEven :
      (2 : ℤ) ^ e * Z + 2 =
        2 * ((2 : ℤ) ^ (e - 1) * Z + 1) := by
    rw [hExp, pow_succ]
    ring_nf
    simp
  have hRhs :
      A.terminalCarryRhs =
        (2 : ℤ) ^ e * Z + 2 := by
    unfold terminalCarryRhs
    simp only [c, e, Z]
  refine ⟨(2 : ℤ) ^ (e - 1) * Z + 1, ?_⟩
  rw [hRhs]
  exact hEven

/--
actual attached terminal mountain の共通 cofactor `a`。

rise start と terminal predecessor は同じ `a` で

  X_s + 1     = 2^W a,
  X_(c-1) + 1 = 2 * 3^(W-1) a

と exact に書ける。
-/
theorem exists_terminalMountainCofactor
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart : 0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    ∃ a : ℕ,
      0 < a ∧
      MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.straightHenselStart
          (Nat.le_of_lt (by
            simpa using
              (A.straight_index_lt_profile_m
                (i := 0) A.straightHenselWidth_pos))) + 1 =
        2 ^ A.straightHenselWidth * a ∧
      MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
          (Nat.le_of_lt A.terminal_isExposed.lt_m) + 1 =
        2 * 3 ^ (A.straightHenselWidth - 1) * a := by
  let P := M.toPureBProfileObstruction hL
  let W := A.straightHenselWidth
  let Xs :=
    MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.straightHenselStart
      (Nat.le_of_lt (by
        simpa using
          (A.straight_index_lt_profile_m
            (i := 0) A.straightHenselWidth_pos)))
  let Xt :=
    MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
      (Nat.le_of_lt A.terminal_isExposed.lt_m)
  have hW : 0 < W := by
    dsimp [W]
    exact A.straightHenselWidth_pos
  have hLast := A.terminalPred_fused_eq_actualShiftedState M hL hStart
  have hAnchor := A.straightCriticalFusedState_terminalPred_anchor hStart
  have hE : A.terminalCarryRhs = 3 * ((Xt : ℤ) + 1) := by
    dsimp [P, W, Xt] at hLast
    calc
      A.terminalCarryRhs
          = 3 * A.straightCriticalFusedState
              hStart (A.straightHenselWidth - 1) := hAnchor.symm
      _ = 3 *
          ((MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
              (Nat.le_of_lt A.terminal_isExposed.lt_m) : ℤ) + 1) := by
            rw [hLast]
  have hEvenE := A.terminalCarryRhs_even
  have hEvenProd :
      (2 : ℤ) ∣ 3 * ((Xt : ℤ) + 1) := by
    rw [← hE]
    exact hEvenE
  have h23 : IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hEvenXtZ : (2 : ℤ) ∣ (Xt : ℤ) + 1 :=
    h23.dvd_of_dvd_mul_left hEvenProd
  have hEvenXt : 2 ∣ Xt + 1 := by
    exact_mod_cast hEvenXtZ
  have hRise0 :=
    A.actualStraightShiftTransport
      M hL (i := 0) (r := W - 1) (by
        dsimp [W]
        omega)
  have hPredIdx := A.straight_last_eq_terminal
  have hRise :
      2 ^ (W - 1) * (Xt + 1) =
        3 ^ (W - 1) * (Xs + 1) := by
    dsimp [P, W, Xs, Xt] at hRise0 ⊢
    simpa [hPredIdx] using hRise0
  rcases hEvenXt with ⟨t, ht⟩
  have hDvdProd :
      2 ^ W ∣ 3 ^ (W - 1) * (Xs + 1) := by
    refine ⟨t, ?_⟩
    rw [← hRise, ht]
    have hExp : W = (W - 1) + 1 := by omega
    rw [hExp, pow_succ]
    ring_nf
    simp
  have hcop : Nat.Coprime (2 ^ W) (3 ^ (W - 1)) :=
    ((by decide : Nat.Coprime 2 3).pow_left W).pow_right (W - 1)
  have hDvdStart : 2 ^ W ∣ Xs + 1 :=
    hcop.dvd_of_dvd_mul_left hDvdProd
  rcases hDvdStart with ⟨a, haEq⟩
  have haPos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    rw [ha0, mul_zero] at haEq
    omega
  have hTermScaled :
      2 ^ (W - 1) * (Xt + 1) =
        2 ^ (W - 1) * (2 * 3 ^ (W - 1) * a) := by
    calc
      2 ^ (W - 1) * (Xt + 1)
          = 3 ^ (W - 1) * (Xs + 1) := hRise
      _ = 3 ^ (W - 1) * (2 ^ W * a) := by rw [haEq]
      _ = 2 ^ (W - 1) * (2 * 3 ^ (W - 1) * a) := by
        have hExp : W = (W - 1) + 1 := by omega
        rw [hExp, pow_succ]
        ring_nf
        simp
  have hTerm : Xt + 1 = 2 * 3 ^ (W - 1) * a :=
    Nat.mul_left_cancel (Nat.pow_pos (by omega)) hTermScaled
  exact ⟨a, haPos, haEq, hTerm⟩

/-! ## 7. terminal carry RHS の actual mountain exact form -/

/--
terminal carry RHS は actual mountain cofactor `a` により

  E = 2 * 3^W * a

と exact に書ける。
-/
theorem terminalCarryRhs_eq_two_mul_threePow_mul_mountainCofactor
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart : 0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    ∃ a : ℕ,
      0 < a ∧
      A.terminalCarryRhs =
        2 * (3 : ℤ) ^ A.straightHenselWidth * (a : ℤ) := by
  obtain ⟨a, haPos, _hStartCof, hTermCof⟩ :=
    A.exists_terminalMountainCofactor M hL hStart
  let Xt :=
    MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
      (Nat.le_of_lt A.terminal_isExposed.lt_m)
  have hLast := A.terminalPred_fused_eq_actualShiftedState M hL hStart
  have hAnchor := A.straightCriticalFusedState_terminalPred_anchor hStart
  have hE : A.terminalCarryRhs = 3 * ((Xt : ℤ) + 1) := by
    dsimp [Xt] at hLast
    calc
      A.terminalCarryRhs
          = 3 * A.straightCriticalFusedState
              hStart (A.straightHenselWidth - 1) := hAnchor.symm
      _ = 3 *
          ((MinimalActualABObstructionPacket.actualUpperPrefixState M hL A.normalForm.terminal
              (Nat.le_of_lt A.terminal_isExposed.lt_m) : ℤ) + 1) := by
            rw [hLast]
  have hTermZ :
      (Xt : ℤ) + 1 =
        2 * (3 : ℤ) ^ (A.straightHenselWidth - 1) * (a : ℤ) := by
    exact_mod_cast hTermCof
  refine ⟨a, haPos, ?_⟩
  rw [hE, hTermZ]
  have hW :
      A.straightHenselWidth =
        (A.straightHenselWidth - 1) + 1 := by
    have hPos := A.straightHenselWidth_pos
    omega
  rw [hW, pow_succ]
  ring_nf
  simp

/-! ## 8. old terminal-near V-budget は actual branch では不可能 -/

/--
旧 `AttachedTerminalNearAnchorBudgetObligation` の第一 budget

  2^dV * E <= 3^(m+dV+1)

は actual terminal mountain と両立しない。

terminal-near placement から `dV <= m`、width 条件から
`m+dV+1 < W`。一方 `E = 2*3^W*a` (`a>0`) なので
左辺は少なくとも `3^W` であり contradiction。
-/
theorem terminalNearAnchorBudgetV_impossible
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart : 0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {m i j : ℕ}
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth)
    (hiNear : A.straightHenselWidth - (2 * m + 2) ≤ i)
    (hij : i < j)
    (hjEnd : j + m < A.straightHenselWidth)
    (hBudgetV :
      let dV := A.straightHenselWidth - 1 - (j + m)
      (2 : ℤ) ^ dV * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dV + 1)) :
    False := by
  let W := A.straightHenselWidth
  let dV := W - 1 - (j + m)
  have hWidth' : 2 * m + 2 ≤ W := by simpa [W] using hWidth
  have hiNear' : W - (2 * m + 2) ≤ i := by simpa [W] using hiNear
  have hjEnd' : j + m < W := by simpa [W] using hjEnd
  have hdV : dV ≤ m := by
    dsimp [dV]
    omega
  have hExpLt : m + dV + 1 < W := by
    omega
  have hBudgetV' :
      (2 : ℤ) ^ dV * A.terminalCarryRhs ≤
        (3 : ℤ) ^ (m + dV + 1) := by
    simpa [dV, W] using hBudgetV
  obtain ⟨a, haPos, hE⟩ :=
    A.terminalCarryRhs_eq_two_mul_threePow_mul_mountainCofactor
      M hL hStart
  have haOneNat : 1 ≤ a := by omega
  have haOne : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast haOneNat
  have hThreePos : 0 < (3 : ℤ) ^ W := by positivity
  have hTwoA : (1 : ℤ) ≤ 2 * (a : ℤ) := by omega
  have hELower : (3 : ℤ) ^ W ≤ A.terminalCarryRhs := by
    rw [hE]
    calc
      (3 : ℤ) ^ W = (3 : ℤ) ^ W * 1 := by ring
      _ ≤ (3 : ℤ) ^ W * (2 * (a : ℤ)) :=
        mul_le_mul_of_nonneg_left hTwoA (le_of_lt hThreePos)
      _ = 2 * (3 : ℤ) ^ W * (a : ℤ) := by ring
  have hENonneg : 0 ≤ A.terminalCarryRhs :=
    le_trans (le_of_lt hThreePos) hELower
  have hTwoPowOne : (1 : ℤ) ≤ (2 : ℤ) ^ dV := by
    induction dV with
    | zero =>
        norm_num
    | succ n ih =>
        calc
          (1 : ℤ) ≤ (2 : ℤ) ^ n := ih
          _ = (2 : ℤ) ^ n * 1 := by ring
          _ ≤ (2 : ℤ) ^ n * 2 := by
            exact
              mul_le_mul_of_nonneg_left
                (by norm_num : (1 : ℤ) ≤ 2)
                (by positivity)
          _ = (2 : ℤ) ^ (n + 1) := by
            rw [pow_succ]
  have hScaledLower :
      (3 : ℤ) ^ W ≤ (2 : ℤ) ^ dV * A.terminalCarryRhs := by
    calc
      (3 : ℤ) ^ W ≤ A.terminalCarryRhs := hELower
      _ = 1 * A.terminalCarryRhs := by ring
      _ ≤ (2 : ℤ) ^ dV * A.terminalCarryRhs :=
        mul_le_mul_of_nonneg_right hTwoPowOne hENonneg
  have hPowLtNat :
      3 ^ (m + dV + 1) < 3 ^ W := by
    exact Nat.pow_lt_pow_right (by norm_num : 1 < (3 : ℕ)) hExpLt
  have hPowLt :
      (3 : ℤ) ^ (m + dV + 1) < (3 : ℤ) ^ W := by
    exact_mod_cast hPowLtNat
  have hContr :
      (3 : ℤ) ^ W < (3 : ℤ) ^ W :=
    lt_of_le_of_lt (le_trans hScaledLower hBudgetV') hPowLt
  exact (lt_irrefl _ hContr)

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
