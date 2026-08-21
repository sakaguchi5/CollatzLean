import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBFullDepthOriginExclusion
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBLocalSquareRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianSquareWindow14

set_option linter.style.emptyLine false
/-!
# Pure B terminal arithmetic tail: degree-14 localization from local Sturmian squares

`CriticalSturmianSquareWindow14` が与える phase-uniform initial square root

  N <= r <= C (N+1)^14

を criticalization start `a` の一つ左から取る。

もし square 全体が integral critical tail `[a,m]` に収まれば
`PureBLocalSquareRigidity` により

  2^(r-1) <= 4*yNat.

一方 Rhin の既存 polynomial state bound と `m+1 <= 2^ell` から

  4*yNat <= 2^(16+15 ell).

そこで `N = 18 + 15 ell` と取ると square が tail 内に収まることは不可能。
従って tail length は first such square root の twice-size 未満であり、

  m - criticalizationStart
    <= 2*C*19^14 * (ell+1)^14.

Nat-log form では

  m - criticalizationStart
    <= 2*C*19^14 * (log_2(m+1)+2)^14.

このファイルは旧 degree-210 record packing を使用しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- square-window constant `C` から terminal-tail degree-14 constant を作る。 -/
def terminalSquareLog14Constant
    (W : CriticalSturmianSquareWindow14) : ℕ :=
  2 * W.constant * 19 ^ 14

namespace PureBProfileObstruction

/--
`m+1 <= 2^ell` の下で、既存 Rhin bound から

  4*yNat <= 2^(16+15*ell)

を得る。
-/
theorem four_yNat_le_terminalDyadic15
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {ell : ℕ}
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    4 * P.yNat ≤ 2 ^ (16 + 15 * ell) := by
  have hyBound := P.yNat_le_rhinPolynomial R hy
  have hPow : (P.m + 1) ^ 15 ≤ (2 ^ ell) ^ 15 :=
    Nat.pow_le_pow_left hmSize 15
  have hCore :
      4 * P.yNat ≤ 4 * rhinGapK * (2 ^ ell) ^ 15 := by
    calc
      4 * P.yNat
          ≤ 4 * (rhinGapK * (P.m + 1) ^ 15) :=
        Nat.mul_le_mul_left 4 hyBound
      _ ≤ 4 * rhinGapK * (2 ^ ell) ^ 15 := by
        nlinarith
  have hPowerEq :
      4 * rhinGapK * (2 ^ ell) ^ 15 =
        2 ^ (16 + 15 * ell) := by
    unfold rhinGapK
    norm_num
    rw [← pow_mul]
    have hMul : ell * 15 = 15 * ell := by omega
    rw [hMul, pow_add]
    ring
  rw [hPowerEq] at hCore
  exact hCore

/--
phase-uniform square window があれば、canonical arithmetic critical tail は
直接 degree 14 に局在する。
-/
theorem criticalizationTail_le_dyadicSquareLog14
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart)
    {ell : ℕ}
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.m - P.criticalizationStart ≤
      terminalSquareLog14Constant W * (ell + 1) ^ 14 := by
  let a := P.criticalizationStart
  let N : ℕ := 18 + 15 * ell
  let Bnd : ℕ := W.constant * 19 ^ 14 * (ell + 1) ^ 14

  have hNTwo : 2 ≤ N := by
    dsimp [N]
    omega
  rcases W.exists_square (a - 1) N hNTwo with
    ⟨r, hNr, hrWindow, hSquare⟩

  have hrTwo : 2 ≤ r := le_trans hNTwo hNr
  have hNBase : N + 1 ≤ 19 * (ell + 1) := by
    dsimp [N]
    omega
  have hNPow : (N + 1) ^ 14 ≤ (19 * (ell + 1)) ^ 14 :=
    Nat.pow_le_pow_left hNBase 14
  have hrBnd0 :
      r ≤ W.constant * (19 * (ell + 1)) ^ 14 :=
    le_trans hrWindow (Nat.mul_le_mul_left W.constant hNPow)
  have hMulPow :
      (19 * (ell + 1)) ^ 14 = 19 ^ 14 * (ell + 1) ^ 14 := by
    rw [mul_pow]
  have hrBnd : r ≤ Bnd := by
    dsimp [Bnd]
    rw [hMulPow] at hrBnd0
    simpa [mul_assoc] using hrBnd0

  have hTargetEq :
      terminalSquareLog14Constant W * (ell + 1) ^ 14 = 2 * Bnd := by
    dsimp [terminalSquareLog14Constant, Bnd]
    ring

  rw [hTargetEq]
  by_contra hnot
  have hTailBig : 2 * Bnd < P.m - a := by
    simpa [a] using (show 2 * Bnd < P.m - P.criticalizationStart by omega)
  have hTwoR : 2 * r ≤ 2 * Bnd :=
    Nat.mul_le_mul_left 2 hrBnd
  have hFit : a + 2 * r - 1 ≤ P.m := by
    have haLe : a ≤ P.m := P.criticalizationStart_spec.1
    omega

  have hSquareBound :=
    P.criticalizationStart_square_dyadic_bound
      hy
      hStartPos
      hrTwo
      (by simpa [a] using hFit)
      (by simpa [a] using hSquare)

  have hYBound := P.four_yNat_le_terminalDyadic15 R hy hmSize

  have hExpMid : 17 + 15 * ell ≤ r - 1 := by
    dsimp [N] at hNr
    omega
  have hMidLe :
      2 ^ (17 + 15 * ell) ≤ 2 ^ (r - 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExpMid
  have hStrict :
      2 ^ (16 + 15 * ell) < 2 ^ (17 + 15 * ell) := by
    have hExp : 17 + 15 * ell = (16 + 15 * ell) + 1 := by omega
    rw [hExp, pow_succ]
    have hPos : 0 < 2 ^ (16 + 15 * ell) := by positivity
    nlinarith

  have hContra : 4 * P.yNat < 2 ^ (r - 1) :=
    lt_of_le_of_lt hYBound (lt_of_lt_of_le hStrict hMidLe)
  omega

/--
canonical arithmetic critical tail の Nat-log degree-14 form。
-/
theorem criticalizationTail_le_log14
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart) :
    P.m - P.criticalizationStart ≤
      terminalSquareLog14Constant W *
        (Nat.log 2 (P.m + 1) + 2) ^ 14 := by
  let ell := Nat.log 2 (P.m + 1) + 1
  have hmLt :
      P.m + 1 < 2 ^ (Nat.log 2 (P.m + 1) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (P.m + 1)
  have hmSize : P.m + 1 ≤ 2 ^ ell := by
    dsimp [ell]
    exact Nat.le_of_lt hmLt
  have hMain :=
    P.criticalizationTail_le_dyadicSquareLog14
      W R hy hStartPos hmSize
  simpa [ell, Nat.add_assoc] using hMain

end PureBProfileObstruction

/--
actual minimal B 用 wrapper。
origin full-depth exclusion から criticalization start の positivity を供給する。
-/
theorem MinimalActualABObstructionPacket.criticalizationTail_le_log14_of_squareWindow
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    P.m - P.criticalizationStart ≤
      terminalSquareLog14Constant W *
        (Nat.log 2 (P.m + 1) + 2) ^ 14 := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  exact P.criticalizationTail_le_log14 W R hy hStart

/--
最終 localization summary：quantitative square-window interface の下で、actual B の
arithmetic critical tail は degree-14 logarithmic window に入る。
-/
theorem MinimalActualABObstructionPacket.decisive_terminal_tail_localized_to_log14
    (W : CriticalSturmianSquareWindow14)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ∃ start : ℕ,
      0 < start ∧
      IsIntegralCriticalTail (M.toPureBProfileObstruction hL) start ∧
      (M.toPureBProfileObstruction hL).m - start ≤
        terminalSquareLog14Constant W *
          (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 14 := by
  let P := M.toPureBProfileObstruction hL
  let start := P.criticalizationStart
  have hStart : 0 < start := by
    simpa [start, P] using M.criticalizationStart_pos R hL
  have hTail :=
    M.criticalizationTail_le_log14_of_squareWindow W R hL
  refine ⟨start, hStart, ?_, ?_⟩
  · simpa [start, P] using P.criticalizationStart_spec
  · simpa [start, P] using hTail

end ExternalArithmetic
end CSTMicro
end Collatz2
