import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreRightCarryChain

/-!
# MultiCorner: corrected restarted-branch divisibility

旧版は restarted branch の zero interval を `[s,b)` としていたが、
実際の Case I は `s ≤ a < b` であり `a` は exposed なので `h a > 0`。
従って zero interval は `(a,b)`、すなわち `[a+1,b)` に限られる。

このファイルでは zero bridge と arithmetic corridor を分離する。

* arithmetic: `s ≤ k ≤ c` なら tail `[k,c)` は `3^(c-k)` で割れる。
* geometry: `[u,b)` が zero なら tail `[u,c)` と tail `[b,c)` は一致する。

restarted branch では `u=a+1<b` を取ることで local width `c-b` より
一段深い `3^(c-b+1)` divisibility が得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- depth zero の column は closed numerator の rightmost mass を持たない。 -/
@[simp] theorem profileRightmostColumnMass_eq_zero_of_depth_eq_zero
    (h : ℕ → ℕ)
    (n : ℕ)
    (hZero : h n = 0) :
    profileRightmostColumnMass h n = 0 := by
  simp [profileRightmostColumnMass, hZero]

/-- `[s,s+d)` が zero-depth なら closed numerator は毎回 `3` 倍される。 -/
theorem profileDyadicClosedNumerator_add_eq_threePow_mul_of_zero_interval
    (h : ℕ → ℕ)
    (s d : ℕ)
    (hZero : ∀ j : ℕ, j < d → h (s + j) = 0) :
    profileDyadicClosedNumerator (s + d) h =
      3 ^ d * profileDyadicClosedNumerator s h := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hZeroLast : h (s + d) = 0 :=
        hZero d (by omega)
      have hMass : profileRightmostColumnMass h (s + d) = 0 :=
        profileRightmostColumnMass_eq_zero_of_depth_eq_zero h (s + d) hZeroLast
      have hZeroPrefix : ∀ j : ℕ, j < d → h (s + j) = 0 := by
        intro j hj
        exact hZero j (by omega)
      have hIH := ih hZeroPrefix
      rw [show s + (d + 1) = (s + d) + 1 by omega]
      rw [profileDyadicClosedNumerator_succ_rightCarry]
      rw [hMass, Nat.zero_add, hIH, pow_succ]
      ring

/-- 任意の `s ≤ b` 版。 -/
theorem profileDyadicClosedNumerator_eq_threePow_mul_of_zero_interval
    (h : ℕ → ℕ)
    {s b : ℕ}
    (hsb : s ≤ b)
    (hZero : ∀ k : ℕ, s ≤ k → k < b → h k = 0) :
    profileDyadicClosedNumerator b h =
      3 ^ (b - s) * profileDyadicClosedNumerator s h := by
  have hMain :=
    profileDyadicClosedNumerator_add_eq_threePow_mul_of_zero_interval
      h s (b - s) (by
        intro j hj
        apply hZero (s + j)
        · omega
        · omega)
  have hEq : s + (b - s) = b := by omega
  rw [hEq] at hMain
  exact hMain

/-- cut `b ≤ c` より右の closed contribution。 -/
noncomputable def restartedClosedTailZ
    (P : PureBProfileObstruction)
    (b c : ℕ) : ℤ :=
  (profileDyadicClosedNumerator c P.h : ℤ) -
    (3 : ℤ) ^ (c - b) *
      (profileDyadicClosedNumerator b P.h : ℤ)

/-- 定義から得られる exact prefix/tail split。 -/
theorem profileDyadicClosedNumerator_cast_eq_scaledPrefix_add_restartedTail
    (P : PureBProfileObstruction)
    {b c : ℕ} :
    (profileDyadicClosedNumerator c P.h : ℤ) =
      (3 : ℤ) ^ (c - b) *
          (profileDyadicClosedNumerator b P.h : ℤ) +
        restartedClosedTailZ P b c := by
  unfold restartedClosedTailZ
  ring

/-- `3^r` は `r ≤ R` なら `3^R` を割る。 -/
theorem threePow_dvd_threePow_of_le
    {r R : ℕ}
    (h : r ≤ R) :
    (3 : ℤ) ^ r ∣ (3 : ℤ) ^ R := by
  refine ⟨(3 : ℤ) ^ (R - r), ?_⟩
  have hExp : R = r + (R - r) := by omega
  rw [hExp, pow_add]
  simp

/--
criticalization corridor 内の任意 cut `k` では、tail `[k,c)` 自身が
local width `c-k` の full 3-adic depthを持つ。

zero interval は一切仮定しない。
-/
theorem restartedTail_localWidth_dvd
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hStart : 0 < P.criticalizationStart)
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k ≤ P.terminalCriticalStart) :
    (3 : ℤ) ^ (P.terminalCriticalStart - k) ∣
      restartedClosedTailZ P k P.terminalCriticalStart := by
  have hDeep :
      (3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart) ∣
        (profileDyadicClosedNumerator
          P.terminalCriticalStart P.h : ℤ) := by
    simpa [PureBProfileObstruction.terminalNoncriticalProfileCore] using
      (P.terminalCore_exactThreeAdicOrder hStart).1
  have hExpLe :
      P.terminalCriticalStart - k ≤
        P.terminalCriticalStart - P.criticalizationStart := by
    omega
  have hPowDvd :
      (3 : ℤ) ^ (P.terminalCriticalStart - k) ∣
        (3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart) :=
    threePow_dvd_threePow_of_le hExpLe
  have hCore :
      (3 : ℤ) ^ (P.terminalCriticalStart - k) ∣
        (profileDyadicClosedNumerator
          P.terminalCriticalStart P.h : ℤ) :=
    dvd_trans hPowDvd hDeep
  have hPrefix :
      (3 : ℤ) ^ (P.terminalCriticalStart - k) ∣
        (3 : ℤ) ^ (P.terminalCriticalStart - k) *
          (profileDyadicClosedNumerator k P.h : ℤ) := by
    refine ⟨(profileDyadicClosedNumerator k P.h : ℤ), ?_⟩
    ring
  have hTailEq :
      restartedClosedTailZ P k P.terminalCriticalStart =
        (profileDyadicClosedNumerator
          P.terminalCriticalStart P.h : ℤ) -
          (3 : ℤ) ^ (P.terminalCriticalStart - k) *
            (profileDyadicClosedNumerator k P.h : ℤ) := by
    unfold restartedClosedTailZ
    rfl
  rw [hTailEq]
  exact dvd_sub hCore hPrefix

/--
`[u,b)` が zero なら cut を `u` から `b` へ動かしても右 tail は変わらない。
-/
theorem restartedClosedTailZ_eq_of_zero_interval
    (P : PureBProfileObstruction)
    {u b c : ℕ}
    (hub : u ≤ b)
    (hbc : b ≤ c)
    (hZero : ∀ k : ℕ, u ≤ k → k < b → P.h k = 0) :
    restartedClosedTailZ P u c = restartedClosedTailZ P b c := by
  have hScaleNat :=
    profileDyadicClosedNumerator_eq_threePow_mul_of_zero_interval
      P.h hub hZero
  have hScaleZ :
      (profileDyadicClosedNumerator b P.h : ℤ) =
        (3 : ℤ) ^ (b - u) *
          (profileDyadicClosedNumerator u P.h : ℤ) := by
    exact_mod_cast hScaleNat
  have hExp : c - u = (c - b) + (b - u) := by
    omega
  unfold restartedClosedTailZ
  rw [hScaleZ, hExp, pow_add]
  ring

/-- tail を右へ一列伸ばす exact recurrence。 -/
theorem restartedClosedTailZ_succ
    (P : PureBProfileObstruction)
    {b c : ℕ}
    (hbc : b ≤ c) :
    restartedClosedTailZ P b (c + 1) =
      (profileRightmostColumnMass P.h c : ℤ) +
        3 * restartedClosedTailZ P b c := by
  unfold restartedClosedTailZ
  rw [profileDyadicClosedNumerator_succ_rightCarry]
  push_cast
  have hExp : c + 1 - b = (c - b) + 1 := by omega
  rw [hExp, pow_succ]
  ring

end MultiCorner
end CSTMicro
end Collatz2
