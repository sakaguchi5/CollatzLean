import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTwoCornerHensel
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDefectRecurrence

/-!
# MultiCorner attached branch: carry-normalized tail arithmetic

attached two-corner geometry から canonical Hensel quotient を作る前段。

このファイルでは

* positive corridor 内の非 exposed cut は carry gap が exact に 1、
* closed tail は左端 checkpoint の 2 冪を必ず因子に持つ、
* fixed right endpoint の tail は左端を一列ずらす exact recurrence を持つ、

ことを証明する。

ここではまだ 3-adic quotient 自体は定義しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- admissible profile の checkpoint は relevant interval 上で単調。 -/
theorem profileCheckpoint_le_of_le
    (P : PureBProfileObstruction)
    {i j : ℕ}
    (hij : i ≤ j)
    (hj : j < P.m) :
    profileCheckpoint P.h i ≤ profileCheckpoint P.h j := by
  induction j, hij using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ j hij ih =>
      have hStep :=
        P.admissible.checkpoint_strict
          (k := j)
          (by omega : j + 1 < P.m)
      exact le_trans (ih (by omega)) (Nat.le_of_lt hStep)

/--
一列 mass はその column checkpoint の 2 冪を exact に因子として持つ。
-/
theorem profileRightmostColumnMass_eq_pow_checkpoint_mul
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    profileRightmostColumnMass P.h k =
      2 ^ profileCheckpoint P.h k *
        (2 ^ P.h k - 1) := by
  have hDepth := P.admissible.depth_le hk
  change
    2 ^ beattyIndex k - 2 ^ (beattyIndex k - P.h k) =
      2 ^ profileCheckpoint P.h k * (2 ^ P.h k - 1)
  rw [show profileCheckpoint P.h k = beattyIndex k - P.h k by rfl]
  have hFactor :=
    twoPow_sub_twoPow_eq_factor
      (a := beattyIndex k - P.h k)
      (b := beattyIndex k)
      (by omega : beattyIndex k - P.h k ≤ beattyIndex k)
  rw [hFactor]
  have hDiff :
      beattyIndex k - (beattyIndex k - P.h k) = P.h k := by
    omega
  rw [hDiff]

/-- carry endpoint より左では同じ factorization を carry checkpoint で読める。 -/
theorem profileRightmostColumnMass_eq_pow_carryCheckpoint_mul
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hkc : k < c)
    (hcM : c ≤ P.m) :
    profileRightmostColumnMass P.h k =
      2 ^ carryCheckpoint P c k *
        (2 ^ P.h k - 1) := by
  rw [carryCheckpoint_of_lt P hkc]
  exact profileRightmostColumnMass_eq_pow_checkpoint_mul P (by omega)

/-- 上の Nat factorization を整数環へ持ち上げる。 -/
theorem profileRightmostColumnMass_cast_eq_pow_carryCheckpoint_mul
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hkc : k < c)
    (hcM : c ≤ P.m) :
    (profileRightmostColumnMass P.h k : ℤ) =
      (2 : ℤ) ^ carryCheckpoint P c k *
        ((2 : ℤ) ^ P.h k - 1) := by
  have hNat :=
    profileRightmostColumnMass_eq_pow_carryCheckpoint_mul P hkc hcM
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hPowPos : 0 < 2 ^ P.h k := by positivity
  have hOneLe : 1 ≤ 2 ^ P.h k := by omega
  push_cast at hCast
  rw [Nat.cast_sub hOneLe] at hCast
  push_cast at hCast
  simpa using hCast

/--
cut `k` から右へ `n` columns を積み上げた非負 closed tail。
`restartedClosedTailZ` の Nat-valued realization として使う。
-/
def profileClosedTailNat
    (P : PureBProfileObstruction)
    (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      profileRightmostColumnMass P.h (k + n) +
        3 * profileClosedTailNat P k n

@[simp] theorem profileClosedTailNat_zero
    (P : PureBProfileObstruction)
    (k : ℕ) :
    profileClosedTailNat P k 0 = 0 := rfl

/-- Nat tail は existing integer closed tail と exact に一致する。 -/
theorem profileClosedTailNat_cast_eq_restartedClosedTailZ
    (P : PureBProfileObstruction)
    (k n : ℕ) :
    (profileClosedTailNat P k n : ℤ) =
      restartedClosedTailZ P k (k + n) := by
  induction n with
  | zero =>
      simp [profileClosedTailNat, restartedClosedTailZ]
  | succ n ih =>
      rw [profileClosedTailNat]
      have hRec :=
        restartedClosedTailZ_succ
          P
          (b := k)
          (c := k + n)
          (by omega)
      have hIdx : k + n + 1 = k + (n + 1) := by omega
      rw [hIdx] at hRec
      push_cast
      rw [ih]
      rw [hRec]

/--
Nat tail 全体から左端 checkpoint の 2 冪を外せる。
checkpoint monotonicityだけを使い、attached geometryには依存しない。
-/
theorem twoPow_profileCheckpoint_dvd_profileClosedTailNat
    (P : PureBProfileObstruction)
    {k n : ℕ}
    (hEnd : k + n ≤ P.m) :
    2 ^ profileCheckpoint P.h k ∣
      profileClosedTailNat P k n := by
  induction n with
  | zero =>
      simp [profileClosedTailNat]
  | succ n ih =>
      have hEndPrev : k + n ≤ P.m := by omega
      have hIdxLt : k + n < P.m := by omega
      have hIH := ih hEndPrev
      have hMono :
          profileCheckpoint P.h k ≤
            profileCheckpoint P.h (k + n) :=
        profileCheckpoint_le_of_le P
          (by omega)
          hIdxLt
      have hPowDvd :
          2 ^ profileCheckpoint P.h k ∣
            2 ^ profileCheckpoint P.h (k + n) :=
        pow_dvd_pow 2 hMono
      have hMassEq :=
        profileRightmostColumnMass_eq_pow_checkpoint_mul P hIdxLt
      have hMassDvd :
          2 ^ profileCheckpoint P.h k ∣
            profileRightmostColumnMass P.h (k + n) := by
        rcases hPowDvd with ⟨z, hz⟩
        refine ⟨z * (2 ^ P.h (k + n) - 1), ?_⟩
        rw [hMassEq, hz]
        ring
      rcases hMassDvd with ⟨u, hu⟩
      rcases hIH with ⟨v, hv⟩
      refine ⟨u + 3 * v, ?_⟩
      rw [profileClosedTailNat, hu, hv]
      ring

/--
integer closed tail は left checkpoint の 2 冪で割れる。
これは generic admissible-profile theorem で、attached 固有条件は不要。
-/
theorem restartedClosedTailZ_twoPow_dvd_of_lt
    (P : PureBProfileObstruction)
    {k c : ℕ}
    (hkc : k < c)
    (hcM : c ≤ P.m) :
    (2 : ℤ) ^ profileCheckpoint P.h k ∣
      restartedClosedTailZ P k c := by
  let n := c - k
  have hEnd : k + n ≤ P.m := by
    dsimp [n]
    omega
  have hDvdNat :=
    twoPow_profileCheckpoint_dvd_profileClosedTailNat P
      (k := k) (n := n) hEnd
  rcases hDvdNat with ⟨u, hu⟩
  refine ⟨(u : ℤ), ?_⟩
  have hCast := profileClosedTailNat_cast_eq_restartedClosedTailZ P k n
  have hIdx : k + n = c := by
    dsimp [n]
    omega
  rw [hIdx] at hCast
  rw [← hCast]
  exact_mod_cast hu

/-- endpoint `k=c` を含む carry-checkpoint 版の dyadic divisibility。 -/
theorem restartedClosedTailZ_twoPow_dvd_carryCheckpoint
    (P : PureBProfileObstruction)
    {k c : ℕ}
    (hkc : k ≤ c)
    (hcM : c ≤ P.m) :
    (2 : ℤ) ^ carryCheckpoint P c k ∣
      restartedClosedTailZ P k c := by
  by_cases hEq : k = c
  · subst k
    simp [restartedClosedTailZ]
  · have hLt : k < c := by omega
    rw [carryCheckpoint_of_lt P hLt]
    exact restartedClosedTailZ_twoPow_dvd_of_lt P hLt hcM

/-- carry checkpoint は corridor 内で一段右へ進むと下がらない。 -/
theorem carryCheckpoint_le_succ
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hkc : k < c)
    (hcM : c ≤ P.m) :
    carryCheckpoint P c k ≤ carryCheckpoint P c (k + 1) := by
  by_cases hSucc : k + 1 < c
  · rw [carryCheckpoint_of_lt P hkc]
    rw [carryCheckpoint_of_lt P hSucc]
    have hStrict :=
      P.admissible.checkpoint_strict
        (k := k)
        (by omega : k + 1 < P.m)
    exact Nat.le_of_lt hStrict
  · have hEq : k + 1 = c := by omega
    rw [carryCheckpoint_of_lt P hkc]
    rw [hEq, carryCheckpoint_self]
    have hkM : k < P.m := by omega
    have hDepth := P.admissible.depth_le hkM
    have hSelf :
        profileCheckpoint P.h k ≤ beattyIndex k := by
      unfold profileCheckpoint
      omega
    have hBeatty : beattyIndex k < beattyIndex c :=
      beattyIndex_strictMono hkc
    omega

/-- carry gap の定義を subtraction-free な加法形へ戻す。 -/
theorem carryCheckpoint_add_carryRunGap_eq_succ
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hkc : k < c)
    (hcM : c ≤ P.m) :
    carryCheckpoint P c k + carryRunGap P c k =
      carryCheckpoint P c (k + 1) := by
  have hLe := carryCheckpoint_le_succ P hkc hcM
  unfold carryRunGap
  omega

/--
right endpoint `c` を固定し、left cut を一列右へ進める exact tail recurrence。
-/
theorem restartedClosedTailZ_left_rec
    (P : PureBProfileObstruction)
    {k c : ℕ}
    (hkc : k < c) :
    restartedClosedTailZ P k c =
      (3 : ℤ) ^ (c - (k + 1)) *
          (profileRightmostColumnMass P.h k : ℤ) +
        restartedClosedTailZ P (k + 1) c := by
  have hCarryNat :=
    profileDyadicClosedNumerator_succ_rightCarry P.h k
  have hCarry := congrArg (fun n : ℕ => (n : ℤ)) hCarryNat
  push_cast at hCarry
  have hExp : c - k = (c - (k + 1)) + 1 := by omega
  unfold restartedClosedTailZ
  rw [hCarry, hExp, pow_succ]
  ring

namespace AttachedTwoCornerPacket

/--
previous と terminal の間の positive 非 exposed cut は carry gap が exact に 1。
-/
theorem internal_carryRunGap_eq_one
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {k : ℕ}
    (hPrev : A.normalForm.previous < k)
    (hTerm : k < A.normalForm.terminal) :
    carryRunGap P P.terminalCriticalStart k = 1 := by
  have hkC : k + 1 < P.terminalCriticalStart := by
    rw [← A.terminal_succ_eq_terminalCriticalStart]
    omega
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k + 1 < P.m := by omega
  have hPos : 0 < P.h k :=
    A.samePositiveCorridor
      k
      (by omega)
      (by omega)
  have hStrict :=
    P.admissible.checkpoint_strict
      (k := k)
      hkM
  have hGapPos : 0 < P.profileRunGap k := by
    rw [P.profileRunGap_of_succ_lt hkM]
    exact Nat.sub_pos_of_lt hStrict
  have hNotMem := A.no_exposed_between hPrev hTerm
  have hNotTwo : ¬ 2 ≤ P.profileRunGap k := by
    intro hTwo
    have E : P.IsExposedPredecessorIndex k :=
      ⟨by omega, hPos, hTwo⟩
    exact hNotMem ((P.mem_exposedPredecessorSet_iff).2 E)
  have hGap : P.profileRunGap k = 1 := by omega
  rw [carryRunGap_eq_profileRunGap_of_succ_lt P hkC hkM]
  exact hGap

/--
attached straight interior では depth は一段ごとに据え置きまたは `+1`。
Beatty gap `1/2` と checkpoint gap `1` の差を取った形。
-/
theorem internal_depth_succ_eq_self_or_add_one
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {k : ℕ}
    (hPrev : A.normalForm.previous < k)
    (hkC : k + 1 < P.terminalCriticalStart) :
    P.h (k + 1) = P.h k ∨
      P.h (k + 1) = P.h k + 1 := by
  have hTerm : k < A.normalForm.terminal := by
    rw [A.terminal_eq]
    omega
  have hGap := A.internal_carryRunGap_eq_one hPrev hTerm
  have hGap' :
      profileCheckpoint P.h (k + 1) -
          profileCheckpoint P.h k = 1 := by
    rw [← carryRunGap_of_succ_lt P hkC]
    exact hGap
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k + 1 < P.m := by omega
  have hDepth0 := P.admissible.depth_le (by omega : k < P.m)
  have hDepth1 := P.admissible.depth_le hkM
  rcases beattyIndex_succ_eq_add_one_or_two k with hBeatty | hBeatty
  · left
    unfold profileCheckpoint at hGap'
    rw [hBeatty] at hGap'
    omega
  · right
    unfold profileCheckpoint at hGap'
    rw [hBeatty] at hGap'
    omega

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
