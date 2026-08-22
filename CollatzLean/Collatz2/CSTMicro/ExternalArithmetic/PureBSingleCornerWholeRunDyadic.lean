import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerSmallRootReduction
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerCriticalizationRun

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: whole straight run の actual dyadic reduction

`|E(B)| = 1` では positive support は exactly `[b,c)` で、

  n = c - b = S.width

と置くと、checkpoint は

  p_k = beta(b) - 1 + (k-b),  b <= k < c

という一本の直線になる。

したがって actual exponent word の区間

  [b,c-1)

は長さ `n-1`、total two-depth も `n-1` なので、validity から
`[1,1,...,1]` そのものになる。既存の actual realization lemma
`oneRun_dvd_realizedPrefixState_add_one` により block start state `X_b` は

  2^(n-1) | X_b + 1

を満たす。

さらに既存の critical-prefix affine bound から

  X_b <= 4 * (R_B + b)

を得る。

この二つを一つの packet に固定する。Rhin の既存 global representative bound を
組み合わせれば無条件に

  n <= 18 + 15*ell

となり、`m <= 6465` では `ell=13` を使って

  n <= 213

まで落ちる。

一方、目標の sharp seed

  2^(n-1) <= 8*n^14*2^ell

に本当に追加で必要なのは

  4*(R_B+b)+1 <= 8*n^14*2^ell

という local representative bound だけである。この一点を
`SingleCornerLocalRhin14Bound` として明示的に隔離する。
これは仮定を隠すためではなく、次に証明すべき local Rhin/Farey lemma の正確な型である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
whole single-corner straight run が与える actual start-state packet。

* `2^(width-1) | X_b+1`
* `X_b <= 4*(R_B+b)`

を同時に保持する。
-/
theorem singleCorner_wholeRun_state_packet
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket) :
    ∃ xb : ℕ,
      2 ^ (S.width - 1) ∣ xb + 1 ∧
      xb ≤
        4 * (M.actual.firstFailureEdge.step.edge.upperR + S.b) := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let b := S.b
  let r := S.width - 1

  have hWidthPos : 0 < S.width := S.width_pos
  have hBC := S.b_add_width_eq_terminalStart
  have hrEq : b + r = P.terminalCriticalStart - 1 := by
    dsimp [b, r]
    simpa [P] using (show S.b + (S.width - 1) =
      (M.toPureBProfileObstruction hL).terminalCriticalStart - 1 by
        have h := S.b_add_width_eq_terminalStart
        omega)

  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : b < P.m := by
    dsimp [b]
    exact lt_of_lt_of_le S.b_lt_c hcLeM
  have hEndM : b + r < P.m := by
    rw [hrEq]
    have hcPos : 0 < P.terminalCriticalStart := by
      have hbLt : S.b < P.terminalCriticalStart := S.b_lt_c
      omega
    omega

  have hmW : Collatz2.Word.oddSteps w = P.m := by
    simpa [w, F, P] using M.actualUpperExponentWord_oddSteps_eq_profile_m hL
  have hbW : b ≤ Collatz2.Word.oddSteps w := by
    rw [hmW]
    omega
  have hbrW : b + r ≤ Collatz2.Word.oddSteps w := by
    rw [hmW]
    omega

  have hReal :
      Collatz2.Word.Realizes w
        F.step.edge.upperR
        (F.step.edge.upperR + F.upperNormalizedDefectNat) := by
    simpa [w] using FirstFailureEdge.upperExponentWord_realizesCanonical F

  have hDepthB :=
    M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hbM
  have hDepthBP :
      Collatz2.Word.prefixTwoDepth w b =
        profileCheckpoint P.h b := by
    simpa [w, F, P] using hDepthB

  have hbOne : P.h b = 1 := by
    simpa [P, b] using S.h_b_eq_one

  have hDepthB' :
      Collatz2.Word.prefixTwoDepth w b = beattyIndex b - 1 := by
    calc
      Collatz2.Word.prefixTwoDepth w b
          = profileCheckpoint P.h b := hDepthBP
      _ = beattyIndex b - 1 := by
          unfold profileCheckpoint
          rw [hbOne]

  have hLineEnd :
      profileCheckpoint P.h (b + r) =
        beattyIndex b - 1 + r := by
    have hbk : S.b ≤ b + r := by
      dsimp [b]
      omega
    have hkc : b + r < P.terminalCriticalStart := by
      rw [hrEq]
      have hcPos : 0 < P.terminalCriticalStart := by
        have hbLt : S.b < P.terminalCriticalStart := S.b_lt_c
        omega
      omega
    have hLine := S.checkpoint_line (b + r) hbk hkc
    have hDiff : b + r - S.b = r := by
      dsimp [b]
      omega
    simpa [b, hDiff] using hLine

  have hDepthEnd :=
    M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hEndM
  have hDepthEnd' :
      Collatz2.Word.prefixTwoDepth w (b + r) =
        beattyIndex b - 1 + r := by
    rw [hDepthEnd]
    exact hLineEnd

  let t : Collatz2.Word := (w.drop b).take r
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
          Collatz2.Word.twoSteps (w.take b) + Collatz2.Word.twoSteps t := by
      rw [hTakeAdd, Collatz2.Word.twoSteps_append]
    change
      Collatz2.Word.twoSteps (w.take (b + r)) =
        Collatz2.Word.twoSteps (w.take b) + Collatz2.Word.twoSteps t at hSum
    change Collatz2.Word.twoSteps (w.take b) = beattyIndex b - 1 at hDepthB'
    change
      Collatz2.Word.twoSteps (w.take (b + r)) =
        beattyIndex b - 1 + r at hDepthEnd'
    omega

  have hrDrop : r ≤ (w.drop b).length := by
    rw [List.length_drop]
    have hwLen : w.length = P.m := by
      simpa [Collatz2.Word.oddSteps] using hmW
    rw [hwLen]
    omega

  have hOddT : Collatz2.Word.oddSteps t = r := by
    dsimp [t, Collatz2.Word.oddSteps]
    exact List.length_take_of_le hrDrop

  have hValidW : Collatz2.Word.Valid w := by
    simpa [w] using F.upperExponentWord_valid
  have hDropValid : Collatz2.Word.Valid (w.drop b) := by
    have hWhole : Collatz2.Word.Valid (w.take b ++ w.drop b) := by
      simpa using hValidW
    exact hWhole.suffix
  have hValidT : Collatz2.Word.Valid t := by
    have hWhole :
        Collatz2.Word.Valid
          ((w.drop b).take r ++ (w.drop b).drop r) := by
      simpa [t] using hDropValid
    exact hWhole.prefix
  have hTEq :
      Collatz2.Word.twoSteps t = Collatz2.Word.oddSteps t := by
    rw [hTwoT, hOddT]

  have hRun0 :=
    word_eq_replicate_one_of_valid_twoSteps_eq_oddSteps
      t hValidT hTEq
  have hRun : t = List.replicate r 1 := by
    simpa [hOddT] using hRun0

  let xb : ℕ := realizedPrefixState hReal b hbW
  have hRunDvd : 2 ^ r ∣ xb + 1 := by
    apply oneRun_dvd_realizedPrefixState_add_one hReal hbW hbrW
    simpa [t] using hRun

  have hRoof :
      ∀ k : ℕ, k < b →
        Collatz2.Word.prefixTwoDepth w k ≤ beattyIndex k := by
    intro k hkb
    have hkM : k < P.m := lt_trans hkb hbM
    have hCoord := M.actualUpperPrefixTwoDepth_eq_profileCheckpoint hL hkM
    rw [hCoord]
    unfold profileCheckpoint
    omega

  have hAffineBound :
      Collatz2.Word.affineConst (w.take b) ≤ b * 3 ^ b :=
    wordAffineConst_take_le_b_mul_threePow hbW hRoof

  have hSpecB := realizedPrefixState_spec hReal b hbW
  change
    3 ^ b * F.step.edge.upperR + Collatz2.Word.affineConst (w.take b) =
      2 ^ Collatz2.Word.twoSteps (w.take b) * xb at hSpecB

  have hBetaPos : 0 < beattyIndex b := by
    have hDepth := P.admissible.depth_le hbM
    rw [hbOne] at hDepth
    omega

  have hRatio :
      3 ^ b ≤ 4 * 2 ^ Collatz2.Word.twoSteps (w.take b) := by
    have hUpper := beattyIndex_upper b
    have hExp : beattyIndex b + 1 = (beattyIndex b - 1) + 2 := by
      omega
    change Collatz2.Word.twoSteps (w.take b) = beattyIndex b - 1 at hDepthB'
    rw [hDepthB']
    calc
      3 ^ b ≤ 2 ^ (beattyIndex b + 1) := hUpper
      _ = 4 * 2 ^ (beattyIndex b - 1) := by
        rw [hExp, pow_add]
        norm_num
        ring

  have hNumerator :
      3 ^ b * F.step.edge.upperR + Collatz2.Word.affineConst (w.take b) ≤
        2 ^ Collatz2.Word.twoSteps (w.take b) *
          (4 * (F.step.edge.upperR + b)) := by
    calc
      3 ^ b * F.step.edge.upperR + Collatz2.Word.affineConst (w.take b)
          ≤ 3 ^ b * F.step.edge.upperR + b * 3 ^ b :=
            Nat.add_le_add_left hAffineBound _
      _ = 3 ^ b * (F.step.edge.upperR + b) := by ring
      _ ≤ (4 * 2 ^ Collatz2.Word.twoSteps (w.take b)) *
            (F.step.edge.upperR + b) :=
          Nat.mul_le_mul_right _ hRatio
      _ = 2 ^ Collatz2.Word.twoSteps (w.take b) *
            (4 * (F.step.edge.upperR + b)) := by ring

  rw [hSpecB] at hNumerator
  have hXBound : xb ≤ 4 * (F.step.edge.upperR + b) := by
    by_contra hnot
    have hgt : 4 * (F.step.edge.upperR + b) < xb := by omega
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hgt
        (by positivity : 0 < 2 ^ Collatz2.Word.twoSteps (w.take b))
    omega

  refine ⟨xb, ?_, ?_⟩
  · simpa [r] using hRunDvd
  · simpa [F, b] using hXBound

/--
whole-run packet と既存 Rhin dyadic representative bound から得る無条件の width bound。

これは sharp `n^14` seed を使わない。
-/
theorem singleCorner_width_le_dyadic15_wholeRun
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    S.width ≤ 18 + 15 * ell := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge

  obtain ⟨xb, hDvd, hXBound⟩ :=
    M.singleCorner_wholeRun_state_packet hL S

  have hPowLe : 2 ^ (S.width - 1) ≤ xb + 1 :=
    Nat.le_of_dvd (by omega) hDvd

  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hyCast : (P.yNat : ℤ) = P.y := P.yNat_cast hy
  have hyEq :
      P.y =
        ((M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          (M.actual.q : ℤ)) := by
    simpa [P] using
      M.toPureBProfileObstruction_y_eq_upperR_add_q hL

  have hRZ : (F.step.edge.upperR : ℤ) ≤ P.y := by
    rw [hyEq]
    change
      (M.actual.firstFailureEdge.step.edge.upperR : ℤ) ≤
        (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
          (M.actual.q : ℤ)
    exact le_add_of_nonneg_right (by positivity)
  rw [← hyCast] at hRZ
  have hRleY : F.step.edge.upperR ≤ P.yNat := by
    exact_mod_cast hRZ

  have hYBound := P.four_yNat_le_terminalDyadic15 R hy hmSize
  have hRPart :
      4 * F.step.edge.upperR ≤ 2 ^ (16 + 15 * ell) :=
    le_trans (Nat.mul_le_mul_left 4 hRleY) hYBound

  have hbLeM : S.b ≤ P.m :=
    le_trans (Nat.le_of_lt S.b_lt_c) P.terminalCriticalStart_spec.1
  have hbPlus : S.b + 1 ≤ 2 ^ ell := by
    have : S.b + 1 ≤ P.m + 1 := by omega
    exact le_trans this hmSize
  have hBPart :
      4 * S.b + 1 ≤ 2 ^ (16 + 15 * ell) := by
    calc
      4 * S.b + 1 ≤ 4 * (S.b + 1) := by omega
      _ ≤ 4 * 2 ^ ell := Nat.mul_le_mul_left 4 hbPlus
      _ = 2 ^ (ell + 2) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (16 + 15 * ell) :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)

  have hXSucc : xb + 1 ≤ 2 ^ (17 + 15 * ell) := by
    have hXBound' :
        xb ≤ 4 * (F.step.edge.upperR + S.b) := by
      simpa [F] using hXBound
    calc
      xb + 1 ≤ 4 * F.step.edge.upperR + (4 * S.b + 1) := by
        omega
      _ ≤ 2 ^ (16 + 15 * ell) + 2 ^ (16 + 15 * ell) :=
        Nat.add_le_add hRPart hBPart
      _ = 2 ^ (17 + 15 * ell) := by
        have hExp : 17 + 15 * ell = (16 + 15 * ell) + 1 := by omega
        rw [hExp, pow_succ]
        ring

  have hPowBound :
      2 ^ (S.width - 1) ≤ 2 ^ (17 + 15 * ell) :=
    le_trans hPowLe hXSucc
  have hExpLe : S.width - 1 ≤ 17 + 15 * ell :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPowBound
  have hWidthPos := S.width_pos
  omega

/--
finite residue `m <= 6465` では whole-run width は無条件に `213` 以下。

`6465+1 < 2^13` を使い `ell=13` を固定する。
-/
theorem singleCorner_width_le_213_of_m_le_6465
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hm :
      (M.toPureBProfileObstruction hL).m ≤ 6465) :
    S.width ≤ 213 := by
  have hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ 13 := by
    norm_num
    omega
  have h :=
    M.singleCorner_width_le_dyadic15_wholeRun
      R hL S hmSize
  norm_num at h ⊢
  exact h

/--
sharp width seed に残る唯一の local arithmetic target。

whole-run start state は `X_b <= 4*(R_B+b)` まで既に actual に制御できる。
従ってこの不等式を local Rhin/Farey geometry から示せば、直ちに
`2^(width-1) <= 8*width^14*2^ell` が従う。
-/
def SingleCornerLocalRhin14Bound
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (ell : ℕ) : Prop :=
  (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell →
    4 * (M.actual.firstFailureEdge.step.edge.upperR + S.b) + 1 ≤
      8 * S.width ^ 14 * 2 ^ ell

/--
local Rhin target が得られれば、whole actual straight run は目的の sharp dyadic seed を満たす。
-/
theorem singleCorner_actual_dyadicSeed
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hLocal : M.SingleCornerLocalRhin14Bound hL S ell) :
    2 ^ (S.width - 1) ≤
      8 * S.width ^ 14 * 2 ^ ell := by
  obtain ⟨xb, hDvd, hXBound⟩ :=
    M.singleCorner_wholeRun_state_packet hL S
  have hPowLe : 2 ^ (S.width - 1) ≤ xb + 1 :=
    Nat.le_of_dvd (by omega) hDvd
  have hXLocal :
      xb + 1 ≤
        4 * (M.actual.firstFailureEdge.step.edge.upperR + S.b) + 1 := by
    omega
  exact le_trans (le_trans hPowLe hXLocal) (hLocal hmSize)

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
