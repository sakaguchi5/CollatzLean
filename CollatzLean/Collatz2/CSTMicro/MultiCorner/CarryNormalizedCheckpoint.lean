import CollatzLean.Collatz2.CSTMicro.MultiCorner.TerminalLastTwoExposedNormalForm

/-!
# MultiCorner: carry-normalized checkpoint

exposed predecessor 判定で使う actual endpoint は `p_m = H` だが、
terminal-core の右 carry を critical roof で閉じるときは endpoint を `beta(c)` に置く。
この二つを同じ `profileRunGap` として扱わないための専用座標層。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
carry corridor `[0,c]` 用 checkpoint。
`k<c` では ordinary profile checkpoint、right endpoint `c` では critical roof `beta(c)`。
-/
noncomputable def carryCheckpoint
    (P : PureBProfileObstruction)
    (c k : ℕ) : ℕ :=
  if k < c then profileCheckpoint P.h k else beattyIndex c

/-- carry-normalized consecutive checkpoint gap。 -/
noncomputable def carryRunGap
    (P : PureBProfileObstruction)
    (c k : ℕ) : ℕ :=
  carryCheckpoint P c (k + 1) - carryCheckpoint P c k

@[simp] theorem carryCheckpoint_of_lt
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hk : k < c) :
    carryCheckpoint P c k = profileCheckpoint P.h k := by
  simp [carryCheckpoint, hk]

@[simp] theorem carryCheckpoint_of_ge
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hk : c ≤ k) :
    carryCheckpoint P c k = beattyIndex c := by
  simp [carryCheckpoint, not_lt.mpr hk]

@[simp] theorem carryCheckpoint_self
    (P : PureBProfileObstruction)
    (c : ℕ) :
    carryCheckpoint P c c = beattyIndex c := by
  simp [carryCheckpoint]

/-- corridor interior では ordinary profile checkpoints の差そのもの。 -/
theorem carryRunGap_of_succ_lt
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hk : k + 1 < c) :
    carryRunGap P c k =
      profileCheckpoint P.h (k + 1) - profileCheckpoint P.h k := by
  have hk0 : k < c := by omega
  unfold carryRunGap
  rw [carryCheckpoint_of_lt P hk]
  rw [carryCheckpoint_of_lt P hk0]

/-- corridor の right endpoint へ入る最後の gap。 -/
theorem carryRunGap_of_succ_eq
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hk : k + 1 = c) :
    carryRunGap P c k =
      beattyIndex c - profileCheckpoint P.h k := by
  have hk0 : k < c := by omega
  unfold carryRunGap
  rw [hk, carryCheckpoint_self]
  rw [carryCheckpoint_of_lt P hk0]

/--
`k+1<c` かつ actual endpoint よりも interior なら、
carry-normalized gap と existing `profileRunGap` は一致する。
-/
theorem carryRunGap_eq_profileRunGap_of_succ_lt
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hkC : k + 1 < c)
    (hkM : k + 1 < P.m) :
    carryRunGap P c k = P.profileRunGap k := by
  rw [carryRunGap_of_succ_lt P hkC]
  rw [P.profileRunGap_of_succ_lt hkM]

/--
terminal critical start `c<m` では `h(c)=0` なので、
right endpoint を `beta(c)` に置いても ordinary `profileRunGap` と一致する。
-/
theorem carryRunGap_terminalCriticalStart_eq_profileRunGap_of_lt_m
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 = P.terminalCriticalStart)
    (hc : P.terminalCriticalStart < P.m) :
    carryRunGap P P.terminalCriticalStart k = P.profileRunGap k := by
  have hZero : P.h P.terminalCriticalStart = 0 :=
    P.terminalCriticalStart_spec.2
      P.terminalCriticalStart
      (by omega)
      hc
  have hCheckpoint :
      profileCheckpoint P.h P.terminalCriticalStart =
        beattyIndex P.terminalCriticalStart := by
    unfold profileCheckpoint
    rw [hZero]
    simp
  rw [carryRunGap_of_succ_eq P hk]
  rw [P.profileRunGap_of_succ_lt (by omega)]
  rw [hk]
  rw [hCheckpoint]

/-- full endpoint では carry checkpoint は `beta(m)`。 -/
theorem carryCheckpoint_m_eq_beatty
    (P : PureBProfileObstruction) :
    carryCheckpoint P P.m P.m = beattyIndex P.m := by
  exact carryCheckpoint_self P P.m

/--
actual endpoint checkpoint `H` と carry endpoint `beta(m)` の差はちょうど一。
これが global terminal endpoint correction。
-/
theorem profileEndpointCheckpoint_m_eq_carryCheckpoint_add_one
    (P : PureBProfileObstruction) :
    P.profileEndpointCheckpoint P.m =
      carryCheckpoint P P.m P.m + 1 := by
  calc
    P.profileEndpointCheckpoint P.m = P.H :=
      P.profileEndpointCheckpoint_m
    _ = beattyIndex P.m + 1 := P.terminal_beatty
    _ = carryCheckpoint P P.m P.m + 1 := by
      rw [carryCheckpoint_m_eq_beatty]

/--
最後の odd run では actual `profileRunGap` は carry-normalized gap より一大きい。
175 の `e_4=3` と carry gap `eBar_4=2` の差を一般形で固定する。
-/
theorem profileRunGap_last_eq_carryRunGap_add_one
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k + 1 = P.m) :
    P.profileRunGap k = carryRunGap P P.m k + 1 := by
  have hk0 : k < P.m := by omega
  have hCheckpointLe :
      profileCheckpoint P.h k ≤ beattyIndex P.m := by
    have hSelf : profileCheckpoint P.h k ≤ beattyIndex k := by
      unfold profileCheckpoint
      omega
    have hBeatty : beattyIndex k < beattyIndex P.m :=
      beattyIndex_strictMono (by omega)
    omega
  rw [P.profileRunGap_of_succ_eq_m hk, P.terminal_beatty]
  rw [carryRunGap_of_succ_eq P hk]
  omega

/-- carry gap `e` に付随する整数 defect numerator `2^e - 2`。 -/
noncomputable def carryDefectNumerator
    (P : PureBProfileObstruction)
    (c k : ℕ) : ℕ :=
  2 ^ carryRunGap P c k - 2

/-- straight carry gap `e=1` では defect numerator は zero。 -/
@[simp] theorem carryDefectNumerator_eq_zero_of_gap_one
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hGap : carryRunGap P c k = 1) :
    carryDefectNumerator P c k = 0 := by
  simp [carryDefectNumerator, hGap]

/-- gap `e=2` の最小 nonstraight defect numerator は `2`。 -/
@[simp] theorem carryDefectNumerator_eq_two_of_gap_two
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (hGap : carryRunGap P c k = 2) :
    carryDefectNumerator P c k = 2 := by
  norm_num [carryDefectNumerator, hGap]

/--
carry corridor の strict interior にある exposed cut は carry gap でも `>=2`。
full endpoint では endpoint correction があるので、この theorem は strict interior に限定する。
-/
theorem two_le_carryRunGap_of_exposed_of_succ_lt
    (P : PureBProfileObstruction)
    {c k : ℕ}
    (E : P.IsExposedPredecessorIndex k)
    (hkC : k + 1 < c)
    (hcM : c ≤ P.m) :
    2 ≤ carryRunGap P c k := by
  have hkM : k + 1 < P.m := by omega
  rw [carryRunGap_eq_profileRunGap_of_succ_lt P hkC hkM]
  exact E.two_le_runGap

end MultiCorner
end CSTMicro
end Collatz2
