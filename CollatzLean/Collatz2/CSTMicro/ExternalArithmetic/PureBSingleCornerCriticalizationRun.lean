import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerActualLeftPrefix
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailLog14

set_option linter.style.emptyLine false
/-!
# Pure B single-corner: criticalization start is O(log m) to the right of b

single-corner packet の straight support `[b,c)` と arithmetic criticalization start
`a = criticalizationStart` を比較する。

`b < a` の場合、checkpoint line により odd-only exponent word の区間

  [b, a-1)

は長さ `r=a-b-1`、total two-depth も exact に `r` になる。valid exponent はすべて
positive なので、この区間は `1,1,...,1` そのもの。

actual canonical prefix state `X_b` について therefore

  2^r | X_b + 1.

一方 first-passage prefix affine numerator の粗い bound と Rhin の既存 state boundから

  X_b + 1 <= 2^(17+15*ell)

を得る。従って

  criticalizationStart - b <= 18 + 15*ell.
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. elementary odd-only helpers -/

/-- valid exponent word では odd step 数は total two-depth 以下。 -/
theorem wordOddSteps_le_twoSteps_of_valid
    (w : Collatz2.Word)
    (hValid : Collatz2.Word.Valid w) :
    Collatz2.Word.oddSteps w ≤ Collatz2.Word.twoSteps w := by
  induction w with
  | nil => simp
  | cons e t ih =>
      have he : 0 < e := hValid e (by simp)
      have htValid : Collatz2.Word.Valid t := by
        intro a ha
        exact hValid a (by simp [ha])
      have hTail := ih htValid
      simp only [Collatz2.Word.oddSteps_cons, Collatz2.Word.twoSteps_cons]
      omega

/-- positive exponents で `sum = length` なら全 exponent は exact に 1。 -/
theorem word_eq_replicate_one_of_valid_twoSteps_eq_oddSteps
    (w : Collatz2.Word)
    (hValid : Collatz2.Word.Valid w)
    (hEq : Collatz2.Word.twoSteps w = Collatz2.Word.oddSteps w) :
    w = List.replicate (Collatz2.Word.oddSteps w) 1 := by
  induction w with
  | nil => simp [Collatz2.Word.oddSteps]
  | cons e t ih =>
      have he : 0 < e := hValid e (by simp)
      have htValid : Collatz2.Word.Valid t := by
        intro a ha
        exact hValid a (by simp [ha])
      have hTailLe := wordOddSteps_le_twoSteps_of_valid t htValid
      have hEqRaw :
          e + Collatz2.Word.twoSteps t =
            Collatz2.Word.oddSteps t + 1 := by
        simpa [Collatz2.Word.twoSteps_cons, Collatz2.Word.oddSteps_cons] using hEq
      have heOne : e = 1 := by omega
      have hTailEq :
          Collatz2.Word.twoSteps t = Collatz2.Word.oddSteps t := by
        omega
      have hIH := ih htValid hTailEq
      subst e
      rw [hIH]
      simp [Collatz2.Word.oddSteps]
      rfl

/-- all-one exponent block の affine constant の signed closed form。 -/
theorem wordAffineConst_replicate_one_cast
    (r : ℕ) :
    (Collatz2.Word.affineConst (List.replicate r 1) : ℤ) =
      (3 : ℤ) ^ r - (2 : ℤ) ^ r := by
  induction r with
  | zero => simp only [List.replicate_zero, Word.affineConst_nil,
                        CharP.cast_eq_zero, pow_zero, sub_self]
  | succ r ih =>
      simp only [List.replicate_succ, Collatz2.Word.affineConst_cons,
        Collatz2.Word.oddSteps, List.length_replicate]
      push_cast
      rw [ih, pow_succ, pow_succ]
      ring

/--
consecutive exponent-1 block では shifted state `X+1` が exact に
`3^r / 2^r` で transport される。

これは divisibility より強い exact equality。
-/
theorem oneRun_exact_shift_transport
    {w : Collatz2.Word}
    {x y b r : ℕ}
    (hReal : Collatz2.Word.Realizes w x y)
    (hb : b ≤ Collatz2.Word.oddSteps w)
    (hbr : b + r ≤ Collatz2.Word.oddSteps w)
    (hRun : (w.drop b).take r = List.replicate r 1) :
    2 ^ r *
        (realizedPrefixState hReal (b + r) hbr + 1) =
      3 ^ r *
        (realizedPrefixState hReal b hb + 1) := by
  let t : Collatz2.Word := (w.drop b).take r
  let xb : ℕ := realizedPrefixState hReal b hb
  let xe : ℕ := realizedPrefixState hReal (b + r) hbr

  have hInterval :=
    realizedPrefixState_interval_spec
      (w := w) (x := x) (y := y)
      (b := b) (r := r) hReal hb hbr

  have htRun :
      t = List.replicate r 1 := by
    simpa [t] using hRun

  have htTwo :
      Collatz2.Word.twoSteps t = r := by
    rw [htRun]
    simp [Collatz2.Word.twoSteps]

  change
    2 ^ Collatz2.Word.twoSteps t * xe =
      3 ^ r * xb + Collatz2.Word.affineConst t at hInterval

  have hIntervalZ :=
    congrArg (fun n : ℕ => (n : ℤ)) hInterval
  push_cast at hIntervalZ
  rw [htTwo] at hIntervalZ

  have hAffineRun :
      (Collatz2.Word.affineConst t : ℤ) =
        (3 : ℤ) ^ r - (2 : ℤ) ^ r := by
    rw [htRun]
    exact wordAffineConst_replicate_one_cast r

  rw [hAffineRun] at hIntervalZ

  have hShiftZ :
      (2 : ℤ) ^ r * ((xe : ℤ) + 1) =
        (3 : ℤ) ^ r * ((xb : ℤ) + 1) := by
    linarith

  have hShiftNat :
      2 ^ r * (xe + 1) =
        3 ^ r * (xb + 1) := by
    exact_mod_cast hShiftZ

  simpa [xb, xe] using hShiftNat

/--
actual realization の consecutive exponent-1 block は、その block start state に
`2^r | X+1` を強制する。
-/
theorem oneRun_dvd_realizedPrefixState_add_one
    {w : Collatz2.Word}
    {x y b r : ℕ}
    (hReal : Collatz2.Word.Realizes w x y)
    (hb : b ≤ Collatz2.Word.oddSteps w)
    (hbr : b + r ≤ Collatz2.Word.oddSteps w)
    (hRun : (w.drop b).take r = List.replicate r 1) :
    2 ^ r ∣ realizedPrefixState hReal b hb + 1 := by
  let xb : ℕ := realizedPrefixState hReal b hb
  let xe : ℕ := realizedPrefixState hReal (b + r) hbr

  have hShiftNat :=
    oneRun_exact_shift_transport
      (w := w) (x := x) (y := y)
      (b := b) (r := r)
      hReal hb hbr hRun

  have hShift :=
    congrArg (fun n : ℕ => (n : ℤ)) hShiftNat
  push_cast at hShift

  have hScaled :
      (2 : ℤ) ^ r ∣
        (3 : ℤ) ^ r * ((xb : ℤ) + 1) := by
    refine ⟨(xe : ℤ) + 1, ?_⟩
    exact hShift.symm

  have h23 :
      IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num

  have hcopLeft :
      IsCoprime ((2 : ℤ) ^ r) (3 : ℤ) :=
    h23.pow_left

  have hcop :
      IsCoprime ((2 : ℤ) ^ r) ((3 : ℤ) ^ r) :=
    hcopLeft.pow_right

  have hTargetZ :
      (2 : ℤ) ^ r ∣ (xb : ℤ) + 1 :=
    hcop.dvd_of_dvd_mul_left hScaled

  have hTargetNat :
      2 ^ r ∣ xb + 1 := by
    exact_mod_cast hTargetZ

  simpa [xb] using hTargetNat


/--
roof 以下の odd-prefix affine constant は critical prefix numerator 以下。

coarse bound `b * 3^b` に落とす前の exact comparison。
-/
theorem wordAffineConst_take_le_criticalPrefixPhiNat
    {w : Collatz2.Word}
    {b : ℕ}
    (hb : b ≤ Collatz2.Word.oddSteps w)
    (hRoof :
      ∀ k : ℕ, k < b →
        Collatz2.Word.prefixTwoDepth w k ≤ beattyIndex k) :
    Collatz2.Word.affineConst (w.take b) ≤ criticalPrefixPhiNat b := by
  let u : Collatz2.Word := w.take b
  have hbLen : b ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hb
  have huOdd : Collatz2.Word.oddSteps u = b := by
    dsimp [u, Collatz2.Word.oddSteps]
    exact List.length_take_of_le hbLen
  rw [← wordAffinePrefixNumerator_eq_affineConst u]
  unfold wordAffinePrefixNumerator criticalPrefixPhiNat
  rw [huOdd]
  apply Finset.sum_le_sum
  intro k hkMem
  have hk : k < b := Finset.mem_range.mp hkMem
  have hTake :
      Collatz2.Word.prefixTwoDepth u k =
        Collatz2.Word.prefixTwoDepth w k := by
    dsimp [u]
    unfold Collatz2.Word.prefixTwoDepth
    rw [List.take_take]
    rw [min_eq_left (Nat.le_of_lt hk)]
  have hDepth :
      Collatz2.Word.prefixTwoDepth u k ≤ beattyIndex k := by
    rw [hTake]
    exact hRoof k hk
  unfold wordAffinePrefixTerm
  rw [huOdd]
  exact
    Nat.mul_le_mul_right
      (3 ^ (b - (k + 1)))
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth)

/--
roof 以下の odd-prefix affine constant は `b * 3^b` 以下。
-/
theorem wordAffineConst_take_le_b_mul_threePow
    {w : Collatz2.Word}
    {b : ℕ}
    (hb : b ≤ Collatz2.Word.oddSteps w)
    (hRoof :
      ∀ k : ℕ, k < b →
        Collatz2.Word.prefixTwoDepth w k ≤ beattyIndex k) :
    Collatz2.Word.affineConst (w.take b) ≤ b * 3 ^ b := by
  have hCritical :=
    wordAffineConst_take_le_criticalPrefixPhiNat hb hRoof
  calc
    Collatz2.Word.affineConst (w.take b)
        ≤ criticalPrefixPhiNat b := hCritical
    _ ≤ Finset.sum (Finset.range b) (fun _ => 3 ^ b) := by
      unfold criticalPrefixPhiNat
      apply Finset.sum_le_sum
      intro k hkMem
      have hk : k < b := Finset.mem_range.mp hkMem
      have hTwo :
          2 ^ beattyIndex k ≤ 3 ^ k :=
        beattyIndex_lower k
      have hExp : b - (k + 1) ≤ b - k := by
        omega
      have hThree :
          3 ^ (b - (k + 1)) ≤ 3 ^ (b - k) :=
        Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hExp
      calc
        2 ^ beattyIndex k * 3 ^ (b - (k + 1))
            ≤ 3 ^ k * 3 ^ (b - k) :=
          Nat.mul_le_mul hTwo hThree
        _ = 3 ^ b := by
          rw [← pow_add]
          congr 1
          omega
    _ = b * 3 ^ b := by
      simp

/-! ## 2. actual single-corner specialization -/

namespace MinimalActualABObstructionPacket

/--
actual single-corner では arithmetic criticalization start は `b` の右へ
高々 `18+15*ell` しか進めない。
-/
theorem singleCorner_criticalizationStart_sub_b_le_dyadic15
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    (M.toPureBProfileObstruction hL).criticalizationStart - S.b ≤
      18 + 15 * ell := by
  let P := M.toPureBProfileObstruction hL
  let F := M.actual.firstFailureEdge
  let w := F.upperExponentWord
  let a := P.criticalizationStart
  let b := S.b

  by_cases hab : a ≤ b
  · change a - b ≤ 18 + 15 * ell
    omega

  have hba : b < a := by omega
  let r : ℕ := a - b - 1
  have hrEq : b + r = a - 1 := by
    dsimp [r]
    omega
  have haLeC : a ≤ P.terminalCriticalStart :=
    P.criticalizationStart_le_terminalCriticalStart
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : b < P.m :=
    lt_of_lt_of_le S.b_lt_c hcLeM
  have hEndM : b + r < P.m := by
    rw [hrEq]
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

  have hbOne0 :
      (M.toPureBProfileObstruction hL).h S.b = 1 :=
    S.h_b_eq_one

  have hbOne :
      P.h b = 1 := by
    simpa only [P, b] using hbOne0

  have hDepthB' :
      Collatz2.Word.prefixTwoDepth w b =
        beattyIndex b - 1 := by
    calc
      Collatz2.Word.prefixTwoDepth w b
          = profileCheckpoint P.h b := hDepthBP
      _ = beattyIndex b - 1 := by
          unfold profileCheckpoint
          rw [hbOne]
  have hLineEnd :
      profileCheckpoint P.h (b + r) =
        beattyIndex b - 1 + r := by
    have hbk : S.b ≤ b + r := by simp [b]
    have hkc : b + r < P.terminalCriticalStart := by
      rw [hrEq]
      omega
    have hLine := S.checkpoint_line (b + r) hbk hkc
    have hDiff : b + r - S.b = r := by simp [b]
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
      Collatz2.Word.twoSteps (w.take (b + r)) = beattyIndex b - 1 + r at hDepthEnd'
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
      Collatz2.Word.twoSteps t =
        Collatz2.Word.oddSteps t := by
    rw [hTwoT, hOddT]

  have hRun0 :=
    word_eq_replicate_one_of_valid_twoSteps_eq_oddSteps
      t hValidT hTEq

  have hRun :
      t = List.replicate r 1 := by
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
    have hbOne := S.h_b_eq_one
    rw [hbOne] at hDepth
    omega
  have hRatio :
      3 ^ b ≤ 4 * 2 ^ Collatz2.Word.twoSteps (w.take b) := by
    have hUpper := beattyIndex_upper b
    have hExp : beattyIndex b + 1 = (beattyIndex b - 1) + 2 := by omega
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

  have hbPlus : b + 1 ≤ 2 ^ ell := by
    have : b + 1 ≤ P.m + 1 := by omega
    exact le_trans this hmSize
  have hBPart :
      4 * b + 1 ≤ 2 ^ (16 + 15 * ell) := by
    calc
      4 * b + 1 ≤ 4 * (b + 1) := by omega
      _ ≤ 4 * 2 ^ ell := Nat.mul_le_mul_left 4 hbPlus
      _ = 2 ^ (ell + 2) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (16 + 15 * ell) :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)

  have hXSucc : xb + 1 ≤ 2 ^ (17 + 15 * ell) := by
    calc
      xb + 1 ≤ 4 * F.step.edge.upperR + (4 * b + 1) := by
        have := hXBound
        omega
      _ ≤ 2 ^ (16 + 15 * ell) + 2 ^ (16 + 15 * ell) :=
        Nat.add_le_add hRPart hBPart
      _ = 2 ^ (17 + 15 * ell) := by
        have hExp : 17 + 15 * ell = (16 + 15 * ell) + 1 := by omega
        rw [hExp, pow_succ]
        ring
  have hPowLe : 2 ^ r ≤ xb + 1 :=
    Nat.le_of_dvd (by omega) hRunDvd

  have hExpLe : r ≤ 17 + 15 * ell :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      (le_trans hPowLe hXSucc)

  have hrDef :
      r = a - b - 1 := by
    rfl

  change a - b ≤ 18 + 15 * ell
  omega

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
