import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailLog14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBLocalOneShortSquareRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianOneShortSquareWindowD

set_option linter.style.emptyLine false
set_option exponentiation.threshold 300

/-!
# Pure B terminal tail: one-short window による degree 196 localization

one-short window が

  N <= r <= C*(N+1)^196

を与えるとする。
既存 Rhin state bound は

  4*yNat <= 2^(16+15*ell)

である。一方 one-short rigidity は tail 内に収まる root に対して

  2^(r-2) <= 4*yNat

を要求する。

そこで

  N = 19 + 15*ell

と取れば `r-2 >= 17+15*ell` となり矛盾する。
従って criticalization tail は最初の one-short root の二倍未満に局在し、

  m-a <= 2*C*20^196*(ell+1)^196

を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- one-short window constant から terminal-tail degree 196 constant を作る。 -/
def terminalOneShortSquareLog196Constant
    (W : CriticalSturmianOneShortSquareWindow196) : ℕ :=
  2 * W.constant * 20 ^ 196

namespace PureBProfileObstruction

/--
one-short window の `N = 19 + 15ℓ` に対する root bound を
terminal-tail 用の canonical polynomial bound に変換する。
-/
theorem oneShortSquareWindow196_root_le_terminalBound
    (W : CriticalSturmianOneShortSquareWindow196)
    {ell r : ℕ}
    (hrWindow :
      r ≤ W.constant * ((19 + 15 * ell) + 1) ^ 196) :
    r ≤
      W.constant * 20 ^ 196 * (ell + 1) ^ 196 := by
  have hNBase :
      (19 + 15 * ell) + 1 ≤ 20 * (ell + 1) := by
    omega
  have hNPow :
      ((19 + 15 * ell) + 1) ^ 196 ≤
        (20 * (ell + 1)) ^ 196 :=
    Nat.pow_le_pow_left hNBase 196
  have hrBnd :
      r ≤ W.constant * (20 * (ell + 1)) ^ 196 :=
    le_trans hrWindow
      (Nat.mul_le_mul_left W.constant hNPow)
  rw [mul_pow] at hrBnd
  simpa [mul_assoc] using hrBnd

/--
terminal one-short constant を、root bound のちょうど 2 倍の形に展開する。
-/
theorem terminalOneShortSquareLog196Constant_mul_pow_eq
    (W : CriticalSturmianOneShortSquareWindow196)
    (ell : ℕ) :
    terminalOneShortSquareLog196Constant W *
        (ell + 1) ^ 196 =
      2 *
        (W.constant * 20 ^ 196 * (ell + 1) ^ 196) := by
  unfold terminalOneShortSquareLog196Constant
  ring

/--
`2r` が criticalization tail より真に短ければ、
one-short square が要求する `a + 2r - 2` まで terminal range に入る。
-/
theorem criticalizationStart_two_root_fit
    (P : PureBProfileObstruction)
    {r : ℕ}
    (hTail :
      2 * r <
        P.m - P.criticalizationStart) :
    P.criticalizationStart + 2 * r - 2 ≤ P.m := by
  have haLe :
      P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  omega

/--
`r ≥ 19 + 15ℓ` なら、terminal dyadic exponent `16 + 15ℓ` は
one-short square が与える exponent `r - 2` より真に小さい。
-/
theorem oneShortSquare196_terminalDyadic_lt
    {ell r y : ℕ}
    (hNr : 19 + 15 * ell ≤ r)
    (hYBound :
      4 * y ≤ 2 ^ (16 + 15 * ell)) :
    4 * y < 2 ^ (r - 2) := by
  have hExpMid :
      17 + 15 * ell ≤ r - 2 := by
    omega
  have hMidLe :
      2 ^ (17 + 15 * ell) ≤
        2 ^ (r - 2) :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ)) hExpMid
  have hStrict :
      2 ^ (16 + 15 * ell) <
        2 ^ (17 + 15 * ell) := by
    have hExp :
        17 + 15 * ell =
          (16 + 15 * ell) + 1 := by
      omega
    rw [hExp, pow_succ]
    have hPos :
        0 < 2 ^ (16 + 15 * ell) := by
      positivity
    nlinarith
  exact
    lt_of_le_of_lt
      hYBound
      (lt_of_lt_of_le hStrict hMidLe)



/--
phase-uniform one-short window から canonical arithmetic critical tail を
degree 196 に局在する。
-/
theorem criticalizationTail_le_dyadicOneShortSquareLog196
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart)
    {ell : ℕ}
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.m - P.criticalizationStart ≤
      terminalOneShortSquareLog196Constant W *
        (ell + 1) ^ 196 := by
  let a : ℕ := P.criticalizationStart
  let N : ℕ := 19 + 15 * ell
  let Bnd : ℕ :=
    W.constant * 20 ^ 196 * (ell + 1) ^ 196

  have hNTwo : 2 ≤ N := by
    dsimp [N]
    omega

  rcases W.exists_oneShort (a - 1) N hNTwo with
    ⟨r, hNr, hrWindow, hOneShort⟩

  have hrTwo : 2 ≤ r :=
    le_trans hNTwo hNr

  have hrBnd : r ≤ Bnd := by
    dsimp [Bnd]
    apply oneShortSquareWindow196_root_le_terminalBound W
    simpa [N] using hrWindow

  have hTargetEq :
      terminalOneShortSquareLog196Constant W *
          (ell + 1) ^ 196 =
        2 * Bnd := by
    dsimp [Bnd]
    exact
      terminalOneShortSquareLog196Constant_mul_pow_eq
        W ell

  rw [hTargetEq]

  by_contra hnot

  have hTailBig :
      2 * Bnd < P.m - a := by
    simpa [a] using
      (show
        2 * Bnd <
          P.m - P.criticalizationStart by
        omega)

  have hTwoRTail :
      2 * r < P.m - a := by
    have hTwoR :
        2 * r ≤ 2 * Bnd :=
      Nat.mul_le_mul_left 2 hrBnd
    exact lt_of_le_of_lt hTwoR hTailBig

  have hFit :
      a + 2 * r - 2 ≤ P.m := by
    simpa [a] using
      criticalizationStart_two_root_fit
        P
        (by simpa [a] using hTwoRTail)

  have hSquareBound :=
    P.criticalizationStart_oneShortSquare_dyadic_bound
      hy hStartPos hrTwo
      (by simpa [a] using hFit)
      (by simpa [a] using hOneShort)

  have hYBound :=
    P.four_yNat_le_terminalDyadic15
      R hy hmSize

  have hNr' :
      19 + 15 * ell ≤ r := by
    simpa [N] using hNr

  have hContra :
      4 * P.yNat < 2 ^ (r - 2) :=
    oneShortSquare196_terminalDyadic_lt
      hNr' hYBound

  omega

/-- canonical arithmetic critical tail の Nat-log degree 196 form。 -/
theorem criticalizationTail_le_log196
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart) :
    P.m - P.criticalizationStart ≤
      terminalOneShortSquareLog196Constant W *
        (Nat.log 2 (P.m + 1) + 2) ^ 196 := by
  let ell := Nat.log 2 (P.m + 1) + 1
  have hmLt :
      P.m + 1 < 2 ^ (Nat.log 2 (P.m + 1) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (P.m + 1)
  have hmSize : P.m + 1 ≤ 2 ^ ell := by
    dsimp [ell]
    exact Nat.le_of_lt hmLt
  have hMain :=
    P.criticalizationTail_le_dyadicOneShortSquareLog196
      W R hy hStartPos hmSize
  simpa [ell, Nat.add_assoc] using hMain

end PureBProfileObstruction

/-- actual minimal B 用 wrapper。 -/
theorem MinimalActualABObstructionPacket.criticalizationTail_le_log196_of_oneShortWindow
    (W : CriticalSturmianOneShortSquareWindow196)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    P.m - P.criticalizationStart ≤
      terminalOneShortSquareLog196Constant W *
        (Nat.log 2 (P.m + 1) + 2) ^ 196 := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  exact P.criticalizationTail_le_log196 W R hy hStart

end ExternalArithmetic
end CSTMicro
end Collatz2
