import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedIntervalFerrersDefectBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRepeatIntervalDefectBridge

/-!
# Attached interval: Ferrers deficit -> Hensel scaled difference

前段では Attached straight interval `[a,b)` に対して

  Ferrers deficit
    -> critical interval defect

を exact に接続した。

一方 `AttachedRepeatIntervalDefectBridge` では、straight suffix の二点
`i < j` と depth offset `Delta` に対して

  2^p M
    = - 2^(delta_i) D[a,b](y)
      - Gamma[a,b] * (Q_i + 2^(delta_i) y)

を持つ。ここで

  p = j - i,
  M = scaledDifference i j Delta 0,
  Q_i = qOne i.

この二式を合成すると、base state `y` は exact に消える。

profile checkpoint を

  c_a = profileCheckpoint P.h a

と書けば `beta(a) = c_a + delta_i` なので、

  FerrersBracket
    = 2^c_a *
        (- 2^p M
         - Gamma[a,b] Q_i
         - (3^p - 2^p)).

さらに parallel-depth relation により

  Gamma[a,b] = 2^(p+Delta) - 3^p

を代入し、`M` と `Q=q+1` を展開すると `Delta` も消えて

  FerrersBracket
    = 2^c_a * (3^p q_i - 2^p q_j)

となる。

したがって actual minimal-B Ferrers deficit は

  F_int[a,b)
    = 3^(m-b) * 2^c_a *
        (3^p q_i - 2^p q_j)

という Hensel endpoint difference そのものになる。

このファイルは exact consistency を固定する層であり、
ここではまだ符号矛盾を主張しない。
後段では `F_int >= 0` と terminal-side smallness を別々に使う。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic
open Collatz2.Word

namespace AttachedTwoCornerPacket

/-! ## 1. critical interval defect -> scaledDifference elimination -/

/--
straight interval 左端で Beatty roof は

  beta(a) = checkpoint(a) + delta_i

と exact に分解される。
-/
theorem beattyIndex_eq_profileCheckpoint_add_henselDelta
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let a := A.straightHenselStart + i
    beattyIndex a =
      profileCheckpoint P.h a + C.delta i := by
  dsimp
  let a := A.straightHenselStart + i
  have hEnd := A.straightHenselStart_add_width
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have haM : a < P.m := by
    dsimp [a]
    omega
  have hDepth : P.h a ≤ beattyIndex a :=
    P.admissible.depth_le haM
  change
    beattyIndex a =
      (beattyIndex a - P.h a) + P.h a
  omega

/--
上の指数分解を 2 冪へ移す。
-/
theorem twoPow_beattyIndex_eq_checkpoint_mul_henselDelta
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let a := A.straightHenselStart + i
    (2 : ℤ) ^ beattyIndex a =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (2 : ℤ) ^ C.delta i := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let a := A.straightHenselStart + i
  have hExp :=
    A.beattyIndex_eq_profileCheckpoint_add_henselDelta
      hStart hi
  dsimp [C, a] at hExp ⊢
  rw [hExp, pow_add]

/--
critical interval defect bridge と Ferrers bracket を合成し、
arbitrary base state `y` を消去した exact normal form。

  Bracket
    = 2^checkpoint(a) *
        (-2^p M - Gamma[a,b] Q_i - (3^p - 2^p)).
-/
theorem straightCheckpointFerrersBracketZ_eq_scaledDifference_form
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    straightCheckpointFerrersBracketZ P.h a p =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (
          - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
          - criticalIntervalGapZ a b * C.qOne i
          - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
        ) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hi : i < A.straightHenselWidth := by
    omega
  have hAp : a + p = b := by
    dsimp [a, b, p]
    omega
  have hPow :=
    A.twoPow_beattyIndex_eq_checkpoint_mul_henselDelta
      hStart hi
  have hHensel :=
    A.scaledDifference_zero_eq_intervalDefect
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
      (0 : ℤ)
  dsimp [C, p, a, b] at hPow hHensel ⊢
  have hHensel0 :
      (2 : ℤ) ^ p * C.scaledDifference i j Delta 0 =
        - (2 : ℤ) ^ C.delta i *
            criticalIntervalPhiZ a b
        - criticalIntervalGapZ a b * C.qOne i := by
    simpa [criticalIntervalDefectZ] using hHensel
  have hPhi :
      (2 : ℤ) ^ C.delta i * criticalIntervalPhiZ a b =
        - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
        - criticalIntervalGapZ a b * C.qOne i := by
    linarith [hHensel0]
  unfold straightCheckpointFerrersBracketZ
  rw [hAp]
  rw [hPow]
  calc
    ((2 : ℤ) ^ profileCheckpoint P.h a *
          (2 : ℤ) ^ C.delta i) *
          criticalIntervalPhiZ a b -
        (2 : ℤ) ^ profileCheckpoint P.h a *
          ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
        =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (
          (2 : ℤ) ^ C.delta i *
              criticalIntervalPhiZ a b
          - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
        ) := by
          ring
    _ =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (
          - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
          - criticalIntervalGapZ a b * C.qOne i
          - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
        ) := by
          rw [hPhi]

/-! ## 2. repeat gap normal form -/

/--
parallel-depth relation から `Gamma = 2^(p+Delta)-3^p` を代入した形。
-/
theorem straightCheckpointFerrersBracketZ_eq_scaledDifference_repeatGap
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    straightCheckpointFerrersBracketZ P.h a p =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (
          - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
          - ((2 : ℤ) ^ (p + Delta) - (3 : ℤ) ^ p) * C.qOne i
          - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
        ) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hBase :=
    A.straightCheckpointFerrersBracketZ_eq_scaledDifference_form
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  have hGap :=
    A.criticalIntervalGapZ_eq_repeatGap
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [C, p, a, b] at hBase hGap ⊢
  rw [hGap] at hBase
  exact hBase

/-! ## 3. endpoint Hensel q normal form -/

/--
scaledDifference と `Q=q+1` を展開すると `Delta` は exact に消える。

  Bracket
    = 2^checkpoint(a) * (3^p q_i - 2^p q_j).
-/
theorem straightCheckpointFerrersBracketZ_eq_henselQEndpoints
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    straightCheckpointFerrersBracketZ P.h a p =
      (2 : ℤ) ^ profileCheckpoint P.h a *
        (
          (3 : ℤ) ^ p * C.q i -
            (2 : ℤ) ^ p * C.q j
        ) := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  have hBase :=
    A.straightCheckpointFerrersBracketZ_eq_scaledDifference_repeatGap
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [C, p, a] at hBase ⊢
  unfold FreeBaseMonotoneHenselChain.scaledDifference
    FreeBaseMonotoneHenselChain.qOne at hBase
  simp only [Nat.add_zero] at hBase
  rw [pow_add] at hBase
  ring_nf at hBase ⊢
  linarith

/-! ## 4. actual minimal-B specialization -/

/--
actual minimal B の integer Ferrers deficit を
Hensel scaledDifference へ直接送る theorem。
-/
theorem integerFerrersDeficitInterval_eq_henselScaledDifference
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    (integerFerrersDeficitInterval w a p : ℤ) =
      (3 : ℤ) ^ (P.m - b) *
        (2 : ℤ) ^ profileCheckpoint P.h a *
          (
            - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
            - criticalIntervalGapZ a b * C.qOne i
            - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
          ) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hEnd : i + p ≤ A.straightHenselWidth := by
    dsimp [p]
    omega
  have hAp : a + p = b := by
    dsimp [a, b, p]
    omega
  have hFerrers :=
    integerFerrersDeficitInterval_eq_attached_straight_formula
      M hL A hEnd
  have hBracket :=
    A.straightCheckpointFerrersBracketZ_eq_scaledDifference_form
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [P, C, p, a, b] at hFerrers hBracket ⊢
  rw [hAp] at hFerrers
  rw [hBracket] at hFerrers
  simpa [mul_assoc] using hFerrers

/--
repeat gap を展開した actual scaledDifference form。
-/
theorem integerFerrersDeficitInterval_eq_henselScaledDifference_repeatGap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    (integerFerrersDeficitInterval w a p : ℤ) =
      (3 : ℤ) ^ (P.m - b) *
        (2 : ℤ) ^ profileCheckpoint P.h a *
          (
            - (2 : ℤ) ^ p * C.scaledDifference i j Delta 0
            - ((2 : ℤ) ^ (p + Delta) - (3 : ℤ) ^ p) * C.qOne i
            - ((3 : ℤ) ^ p - (2 : ℤ) ^ p)
          ) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hBase :=
    integerFerrersDeficitInterval_eq_henselScaledDifference
      M hL A hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  have hGap :=
    A.criticalIntervalGapZ_eq_repeatGap
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [P, C, p, a, b] at hBase hGap ⊢
  rw [hGap] at hBase
  exact hBase

/--
actual minimal B における最終 endpoint form。

  F_int[a,b)
    = 3^(m-b) * 2^checkpoint(a)
        * (3^p q_i - 2^p q_j).
-/
theorem integerFerrersDeficitInterval_eq_henselQEndpoints
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    (integerFerrersDeficitInterval w a p : ℤ) =
      (3 : ℤ) ^ (P.m - b) *
        (2 : ℤ) ^ profileCheckpoint P.h a *
          (
            (3 : ℤ) ^ p * C.q i -
              (2 : ℤ) ^ p * C.q j
          ) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hEnd : i + p ≤ A.straightHenselWidth := by
    dsimp [p]
    omega
  have hAp : a + p = b := by
    dsimp [a, b, p]
    omega
  have hFerrers :=
    integerFerrersDeficitInterval_eq_attached_straight_formula
      M hL A hEnd
  have hBracket :=
    A.straightCheckpointFerrersBracketZ_eq_henselQEndpoints
      hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [P, C, p, a, b] at hFerrers hBracket ⊢
  rw [hAp] at hFerrers
  rw [hBracket] at hFerrers
  simpa [mul_assoc] using hFerrers

/-! ## 5. sign wrapper -/

/--
Ferrers deficit は Nat 由来なので非負。
正の外因子を除けば Hensel endpoint difference も nonnegative。

  0 <= 3^p q_i - 2^p q_j.
-/
theorem henselQEndpointDifference_nonneg_of_actualFerrers
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    0 ≤
      (3 : ℤ) ^ p * C.q i -
        (2 : ℤ) ^ p * C.q j := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hEq :=
    integerFerrersDeficitInterval_eq_henselQEndpoints
      M hL A hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [P, w, C, p, a, b] at hEq ⊢
  have hLeft :
      0 ≤ (integerFerrersDeficitInterval w a p : ℤ) := by
    positivity
  have hFactorPos :
      0 <
        (3 : ℤ) ^ (P.m - b) *
          (2 : ℤ) ^ profileCheckpoint P.h a := by
    positivity
  rw [hEq] at hLeft
  nlinarith

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
