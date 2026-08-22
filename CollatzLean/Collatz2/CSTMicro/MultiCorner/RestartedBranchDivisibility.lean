import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreRightCarryChain

/-!
# MultiCorner: restarted branch divisibility

restarted branch では、左の exposed component と terminal positive component の間に
zero-depth bridge が現れる場合がある。

このファイルでは、その zero bridge を通る closed numerator が exact に 3-power を
獲得することを固定し、terminal core の exact 3-adic order と組み合わせて、
restart 後の terminal contribution 自身に full corridor divisibility が強制されることを示す。

まだここでは contradiction までは主張しない。後段では、この extra divisibility と
terminal component の局所 Hensel state を衝突させる。
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

/--
`[s,s+d)` が zero-depth なら、closed numerator はその区間で毎回 `3` 倍される。

  C_(s+d) = 3^d C_s.
-/
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

/--
cut `b ≤ c` より右に残る contribution を integer difference として定義する。
後で sum 形へ展開できるが、divisibility にはこの exact split interface が十分。
-/
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

/--
`[s,b)` が zero-depth なら、`b` prefix は `s` prefix まで吸収できる。

  C_c = 3^(c-s) C_s + Tail[b,c].
-/
theorem profileDyadicClosedNumerator_cast_eq_scaledZeroBridgePrefix_add_restartedTail
    (P : PureBProfileObstruction)
    {s b c : ℕ}
    (hsb : s ≤ b)
    (hbc : b ≤ c)
    (hZero : ∀ k : ℕ, s ≤ k → k < b → P.h k = 0) :
    (profileDyadicClosedNumerator c P.h : ℤ) =
      (3 : ℤ) ^ (c - s) *
          (profileDyadicClosedNumerator s P.h : ℤ) +
        restartedClosedTailZ P b c := by
  have hScaleNat :=
    profileDyadicClosedNumerator_eq_threePow_mul_of_zero_interval
      P.h hsb hZero
  have hScaleZ :
      (profileDyadicClosedNumerator b P.h : ℤ) =
        (3 : ℤ) ^ (b - s) *
          (profileDyadicClosedNumerator s P.h : ℤ) := by
    exact_mod_cast hScaleNat
  have hExp : c - s = (c - b) + (b - s) := by
    omega
  rw [profileDyadicClosedNumerator_cast_eq_scaledPrefix_add_restartedTail]
  rw [hScaleZ, hExp, pow_add]
  ring

/--
restarted subcase を使うための packet。
`previous < componentStart` が geometric restarted、`[s,b)` zero が arithmetic bridge。
-/
structure RestartedZeroBridgePacket
    (P : PureBProfileObstruction) where
  normalForm : LastTwoExposedNormalForm P
  componentStart : ℕ
  previous_lt_componentStart :
    normalForm.previous < componentStart
  criticalization_le_componentStart :
    P.criticalizationStart ≤ componentStart
  componentStart_le_terminalCriticalStart :
    componentStart ≤ P.terminalCriticalStart
  zero_before_restart :
    ∀ k : ℕ,
      P.criticalizationStart ≤ k →
      k < componentStart →
      P.h k = 0

namespace RestartedZeroBridgePacket

/-- corridor width は local terminal width と restart 前の extra width に分解する。 -/
theorem corridorWidth_eq_terminalWidth_add_extraWidth
    {P : PureBProfileObstruction}
    (B : RestartedZeroBridgePacket P) :
    P.terminalCriticalStart - P.criticalizationStart =
      (P.terminalCriticalStart - B.componentStart) +
        (B.componentStart - P.criticalizationStart) := by
  have hSB := B.criticalization_le_componentStart
  have hBC := B.componentStart_le_terminalCriticalStart
  omega

/--
exact terminal-core order により、restart 後 tail は full corridor `3^(c-s)` で割れる。

これは local terminal width `c-b` に加えて `b-s` 段の extra divisibility を要求する、
restarted branch の arithmetic core。
-/
theorem restartedTail_fullCorridor_dvd
    {P : PureBProfileObstruction}
    (B : RestartedZeroBridgePacket P)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ^
        (P.terminalCriticalStart - P.criticalizationStart) ∣
      restartedClosedTailZ
        P B.componentStart P.terminalCriticalStart := by
  have hCoreDvd :
      (3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart) ∣
        (profileDyadicClosedNumerator
          P.terminalCriticalStart P.h : ℤ) := by
    simpa [PureBProfileObstruction.terminalNoncriticalProfileCore] using
      (P.terminalCore_exactThreeAdicOrder hStart).1
  have hSplit :=
    profileDyadicClosedNumerator_cast_eq_scaledZeroBridgePrefix_add_restartedTail
      P
      B.criticalization_le_componentStart
      B.componentStart_le_terminalCriticalStart
      B.zero_before_restart
  have hPrefixDvd :
      (3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart) ∣
        (3 : ℤ) ^
            (P.terminalCriticalStart - P.criticalizationStart) *
          (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) := by
    refine ⟨(profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ), ?_⟩
    ring
  have hTailEq :
      restartedClosedTailZ P B.componentStart P.terminalCriticalStart =
        (profileDyadicClosedNumerator P.terminalCriticalStart P.h : ℤ) -
          (3 : ℤ) ^
              (P.terminalCriticalStart - P.criticalizationStart) *
            (profileDyadicClosedNumerator P.criticalizationStart P.h : ℤ) := by
    rw [hSplit]
    ring
  rw [hTailEq]
  exact dvd_sub hCoreDvd hPrefixDvd

end RestartedZeroBridgePacket

end MultiCorner
end CSTMicro
end Collatz2
