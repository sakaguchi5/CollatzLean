import CollatzLean.Collatz2.CSTMicro.CarryGeometry.IntervalFerrersDeficitCostBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnLayerScaledExactIntervalRealization
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBActualProfileCoordinateBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyCycleIntervalBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalTailDepthCoordinates

/-!
# Attached straight interval: Ferrers deficit -> critical interval defect

このファイルでは、Attached terminal straight suffix の一つの rank intervalを

* Ferrers 側の integer deficit,
* critical Beatty interval numerator / defect,
* actual minimal-B profile

の三つの座標で exact に同一視する。

中心となる pure profile identity は次である。

`p(k) = profileCheckpoint h k` とし、interval `[u,u+n)` 上で

  p(u+t) = p(u) + t

が成り立つとする。このとき profile cell の dyadic deficit は

  F_profile[u,u+n)
    = 3^(m-(u+n)) *
        (2^beta(u) Phi[u,u+n]
          - 2^p(u) (3^n - 2^n)).

さらに

  criticalIntervalDefectZ u (u+n) y
    = Phi[u,u+n] - Gamma[u,u+n] y

を代入すれば、同じ bracket を critical interval defect で exact に書ける。

最後に minimal actual B + Attached packet では、straight suffix の checkpoint line が
既に exact に `+1` ずつ進むため、この pure theorem を適用し、
今回導入した `integerFerrersDeficitInterval` と exact に同定する。

-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

namespace ExternalArithmetic

/-! ## 1. pure straight-checkpoint interval identity -/

/--
`sum_{t<n} 2^t 3^(n-1-t) = 3^n - 2^n` の整数版。
-/
private theorem twoThreeGeometricSum
    (n : ℕ) :
    Finset.sum (Finset.range n)
        (fun t => (2 : ℤ) ^ t * (3 : ℤ) ^ (n - 1 - t)) =
      (3 : ℤ) ^ n - (2 : ℤ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hHead :
          Finset.sum (Finset.range n)
              (fun t => (2 : ℤ) ^ t * (3 : ℤ) ^ (n + 1 - 1 - t)) =
            3 *
              Finset.sum (Finset.range n)
                (fun t => (2 : ℤ) ^ t * (3 : ℤ) ^ (n - 1 - t)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htLt : t < n := Finset.mem_range.mp ht
        have hExp : n + 1 - 1 - t = (n - 1 - t) + 1 := by
          omega
        rw [hExp, pow_succ]
        ring
      rw [hHead, ih]
      have hLast : n + 1 - 1 - n = 0 := by omega
      rw [hLast]
      simp only [pow_zero, mul_one]
      rw [pow_succ, pow_succ]
      ring

/--
profile の interval Ferrers deficit を Int 上で保持する。
Nat subtraction を避けるため、各 column contribution を signed difference で書く。
-/
def profileFerrersDeficitIntervalZ
    (m : ℕ)
    (h : ℕ → ℕ)
    (u n : ℕ) : ℤ :=
  Finset.sum (Finset.range n)
    (fun t =>
      ((2 : ℤ) ^ beattyIndex (u + t) -
          (2 : ℤ) ^ profileCheckpoint h (u + t)) *
        (3 : ℤ) ^ (m - (u + t + 1)))

/--
Admissible profile では、profile cell の dyadic interval sum は
上の signed Ferrers deficit と exact に一致する。
-/
theorem profileDyadicCellInterval_cast_eq_profileFerrersDeficitIntervalZ
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {u n : ℕ}
    (hRange : u + n ≤ m) :
    (profileDyadicCellInterval m h u n : ℤ) =
      profileFerrersDeficitIntervalZ m h u n := by
  unfold profileDyadicCellInterval profileFerrersDeficitIntervalZ
  push_cast
  apply Finset.sum_congr rfl
  intro t ht
  have htLt : t < n := Finset.mem_range.mp ht
  have hkLt : u + t < m := by omega
  have hDepth := A.depth_le hkLt
  have hClosed :=
    profileDyadicColumnSum_eq_closed
      (m := m)
      (k := u + t)
      (depth := h (u + t))
      hDepth
  have hCast := congrArg (fun z : ℕ => (z : ℤ)) hClosed
  unfold profileDyadicClosedColumn at hCast
  have hCheckpointLe :
      profileCheckpoint h (u + t) ≤ beattyIndex (u + t) := by
    unfold profileCheckpoint
    omega
  have hPowLe :
      2 ^ (beattyIndex (u + t) - h (u + t)) ≤
        2 ^ beattyIndex (u + t) := by
    exact Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (Nat.sub_le _ _)
  rw [Nat.cast_mul] at hCast
  rw [Nat.cast_sub hPowLe] at hCast
  push_cast at hCast
  simpa [profileCheckpoint] using hCast

/-- critical-roof part of a shifted interval. -/
private theorem criticalWeightedInterval_eq
    {m u n : ℕ}
    (hRange : u + n ≤ m) :
    Finset.sum (Finset.range n)
        (fun t =>
          (2 : ℤ) ^ beattyIndex (u + t) *
            (3 : ℤ) ^ (m - (u + t + 1))) =
      (3 : ℤ) ^ (m - (u + n)) *
        (2 : ℤ) ^ beattyIndex u *
          criticalIntervalPhiZ u (u + n) := by
  rw [← beattyCyclePhi_eq_criticalIntervalPhiZ u n]
  unfold beattyCyclePhi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htLt : t < n := Finset.mem_range.mp ht
  have hBeta : beattyIndex u ≤ beattyIndex (u + t) := by
    by_cases ht0 : t = 0
    · subst t
      simp
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaExp :
      beattyIndex (u + t) =
        beattyIndex u +
          (beattyIndex (u + t) - beattyIndex u) := by
    omega
  have hThreeExp :
      m - (u + t + 1) =
        (m - (u + n)) + (n - 1 - t) := by
    omega
  rw [hBetaExp, hThreeExp, pow_add, pow_add]
  ring_nf
  simp only [add_tsub_cancel_left]

/-- straight checkpoint line part of a shifted interval. -/
private theorem straightWeightedInterval_eq
    {m : ℕ}
    {h : ℕ → ℕ}
    {u n : ℕ}
    (hRange : u + n ≤ m)
    (hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint h (u + t) =
          profileCheckpoint h u + t) :
    Finset.sum (Finset.range n)
        (fun t =>
          (2 : ℤ) ^ profileCheckpoint h (u + t) *
            (3 : ℤ) ^ (m - (u + t + 1))) =
      (3 : ℤ) ^ (m - (u + n)) *
        (2 : ℤ) ^ profileCheckpoint h u *
          ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
  rw [← twoThreeGeometricSum n]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htLt : t < n := Finset.mem_range.mp ht
  have hThreeExp :
      m - (u + t + 1) =
        (m - (u + n)) + (n - 1 - t) := by
    omega
  rw [hLine t htLt, pow_add, hThreeExp, pow_add]
  ring

/--
straight checkpoint interval の normalized Ferrers bracket。

  Delta_F(u,n)
    = 2^beta(u) Phi[u,u+n]
      - 2^p(u) (3^n - 2^n).
-/
def straightCheckpointFerrersBracketZ
    (h : ℕ → ℕ)
    (u n : ℕ) : ℤ :=
  (2 : ℤ) ^ beattyIndex u *
      criticalIntervalPhiZ u (u + n) -
    (2 : ℤ) ^ profileCheckpoint h u *
      ((3 : ℤ) ^ n - (2 : ℤ) ^ n)

/--
(4A)
straight checkpoint line を仮定すると、interval Ferrers deficit は
一つの critical interval numerator と一つの geometric term に exact に閉じる。

  F_profile[u,u+n)
    = 3^(m-(u+n)) * Delta_F(u,n).
-/
theorem profileFerrersDeficitIntervalZ_eq_threePow_mul_straightBracket
    {m : ℕ}
    {h : ℕ → ℕ}
    {u n : ℕ}
    (hRange : u + n ≤ m)
    (hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint h (u + t) =
          profileCheckpoint h u + t) :
    profileFerrersDeficitIntervalZ m h u n =
      (3 : ℤ) ^ (m - (u + n)) *
        straightCheckpointFerrersBracketZ h u n := by
  unfold profileFerrersDeficitIntervalZ
    straightCheckpointFerrersBracketZ
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [criticalWeightedInterval_eq hRange]
  rw [straightWeightedInterval_eq hRange hLine]
  ring

/--
cell-level dyadic sum から直接読む (4A)。
-/
theorem profileDyadicCellInterval_cast_eq_threePow_mul_straightBracket
    {m : ℕ}
    {h : ℕ → ℕ}
    (A : AdmissibleSturmianProfile m h)
    {u n : ℕ}
    (hRange : u + n ≤ m)
    (hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint h (u + t) =
          profileCheckpoint h u + t) :
    (profileDyadicCellInterval m h u n : ℤ) =
      (3 : ℤ) ^ (m - (u + n)) *
        straightCheckpointFerrersBracketZ h u n := by
  rw [profileDyadicCellInterval_cast_eq_profileFerrersDeficitIntervalZ A hRange]
  exact
    profileFerrersDeficitIntervalZ_eq_threePow_mul_straightBracket
      hRange hLine

/-! ## 2. criticalIntervalDefectZ を代入した (4C) -/

/--
(4C)
`Phi = Defect + Gap*y` を代入した exact rewrite。
-/
theorem straightCheckpointFerrersBracketZ_eq_intervalDefect
    (h : ℕ → ℕ)
    (u n : ℕ)
    (y : ℤ) :
    straightCheckpointFerrersBracketZ h u n =
      (2 : ℤ) ^ beattyIndex u *
          criticalIntervalDefectZ u (u + n) y +
        (2 : ℤ) ^ beattyIndex u *
          criticalIntervalGapZ u (u + n) * y -
        (2 : ℤ) ^ profileCheckpoint h u *
          ((3 : ℤ) ^ n - (2 : ℤ) ^ n) := by
  unfold straightCheckpointFerrersBracketZ
    criticalIntervalDefectZ
  ring

/--
(4A)+(4C) を一度に使う wrapper。
-/
theorem profileFerrersDeficitIntervalZ_eq_intervalDefect_form
    {m : ℕ}
    {h : ℕ → ℕ}
    {u n : ℕ}
    (hRange : u + n ≤ m)
    (hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint h (u + t) =
          profileCheckpoint h u + t)
    (y : ℤ) :
    profileFerrersDeficitIntervalZ m h u n =
      (3 : ℤ) ^ (m - (u + n)) *
        (
          (2 : ℤ) ^ beattyIndex u *
              criticalIntervalDefectZ u (u + n) y +
            (2 : ℤ) ^ beattyIndex u *
              criticalIntervalGapZ u (u + n) * y -
            (2 : ℤ) ^ profileCheckpoint h u *
              ((3 : ℤ) ^ n - (2 : ℤ) ^ n)
        ) := by
  rw [profileFerrersDeficitIntervalZ_eq_threePow_mul_straightBracket hRange hLine]
  rw [straightCheckpointFerrersBracketZ_eq_intervalDefect]

end ExternalArithmetic

/-! ## 3. minimal actual B + Attached specialization -/

namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
Attached straight suffix の任意 offset interval `[i,i+n)` で checkpoint は exact に直線。

この theorem は `AttachedTerminalTailDepthCoordinates.lean` 内の
`straight_profileCheckpoint_eq_start_add` を public にしたものを利用する。
-/
theorem straight_profileCheckpoint_interval_line
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    ∀ t : ℕ,
      t < n →
      profileCheckpoint P.h (A.straightHenselStart + i + t) =
        profileCheckpoint P.h (A.straightHenselStart + i) + t := by
  intro t ht
  have hi : i < A.straightHenselWidth := by
    omega
  have hit : i + t < A.straightHenselWidth := by
    omega
  have h0 :=
    A.straight_profileCheckpoint_eq_start_add (i := i) hi
  have h1 :=
    A.straight_profileCheckpoint_eq_start_add (i := i + t) hit
  rw [h0]
  simpa [Nat.add_assoc] using h1

/--
Attached straight interval は pure 4A formula をそのまま満たす。
-/
theorem straight_profileDyadicInterval_eq_threePow_mul_bracket
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let u := A.straightHenselStart + i
    (profileDyadicCellInterval P.m P.h u n : ℤ) =
      (3 : ℤ) ^ (P.m - (u + n)) *
        straightCheckpointFerrersBracketZ P.h u n := by
  dsimp
  let u := A.straightHenselStart + i
  have hStartEnd := A.straightHenselStart_add_width
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hRange : u + n ≤ P.m := by
    dsimp [u]
    omega
  have hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint P.h (u + t) =
          profileCheckpoint P.h u + t := by
    intro t ht
    dsimp [u]
    simpa [Nat.add_assoc] using
      A.straight_profileCheckpoint_interval_line hEnd t ht
  exact
    profileDyadicCellInterval_cast_eq_threePow_mul_straightBracket
      P.admissible hRange hLine

/--
Attached straight interval の (4C) specialization。
任意の integer base `y` で critical interval defect form を得る。
-/
theorem straight_profileDyadicInterval_eq_intervalDefect_form
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth)
    (y : ℤ) :
    let u := A.straightHenselStart + i
    (profileDyadicCellInterval P.m P.h u n : ℤ) =
      (3 : ℤ) ^ (P.m - (u + n)) *
        (
          (2 : ℤ) ^ beattyIndex u *
              criticalIntervalDefectZ u (u + n) y +
            (2 : ℤ) ^ beattyIndex u *
              criticalIntervalGapZ u (u + n) * y -
            (2 : ℤ) ^ profileCheckpoint P.h u *
              ((3 : ℤ) ^ n - (2 : ℤ) ^ n)
        ) := by
  dsimp
  let u := A.straightHenselStart + i
  have hStartEnd := A.straightHenselStart_add_width
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hRange : u + n ≤ P.m := by
    dsimp [u]
    omega
  have hLine :
      ∀ t : ℕ,
        t < n →
        profileCheckpoint P.h (u + t) =
          profileCheckpoint P.h u + t := by
    intro t ht
    dsimp [u]
    simpa [Nat.add_assoc] using
      A.straight_profileCheckpoint_interval_line hEnd t ht
  have hPure :=
    profileDyadicCellInterval_cast_eq_threePow_mul_straightBracket
      P.admissible hRange hLine
  rw [straightCheckpointFerrersBracketZ_eq_intervalDefect P.h u n y] at hPure
  exact hPure

/--
minimal actual B + Attached では pure profile interval deficit は
actual exponent word の `integerFerrersDeficitInterval` と exact に一致する。

これが 1--3 の最終 specialization checkpoint。
-/
theorem integerFerrersDeficitInterval_eq_attached_straight_formula
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    (integerFerrersDeficitInterval w u n : ℤ) =
      (3 : ℤ) ^ (P.m - (u + n)) *
        straightCheckpointFerrersBracketZ P.h u n := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  let u := A.straightHenselStart + i
  have hmOdd : P.m = oddCount M.word :=
    M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hOddWord : oddSteps w = oddCount M.word := by
    dsimp [w]
    exact oddSteps_exponentWordOfParity M.word
  have hmW : P.m = oddSteps w := by
    rw [hmOdd, hOddWord]
  have hUpperWord :
      M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
    unfold ActualABObstructionPacket.firstFailureEdge
    unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
    unfold FirstFailureProvenance.toFirstFailureEdge
    dsimp
    exact M.failureStep_upperWord_eq_word
  have hwEq :
      w = M.actual.firstFailureEdge.upperExponentWord := by
    change
      exponentWordOfParity M.word =
        exponentWordOfParity M.actual.firstFailureEdge.step.edge.upperWord
    rw [hUpperWord]
  have hFPw : FirstCrossing w := by
    rw [hwEq]
    exact M.actual.firstFailureEdge.upperExponentWord_firstCrossing
  have hStartEnd := A.straightHenselStart_add_width
  have hStartEndP :
      A.straightHenselStart + A.straightHenselWidth =
        P.terminalCriticalStart := by
    simpa [P] using hStartEnd
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hRangeP : u + n ≤ P.m := by
    dsimp [u]
    omega
  have hRangeW : u + n ≤ oddSteps w := by
    rw [← hmW]
    exact hRangeP
  have hActual :=
    profileDyadicCellInterval_eq_integerFerrersDeficitInterval
      hFPw hRangeW
  have hProfile :
      profileDyadicCellInterval P.m P.h u n =
        profileDyadicCellInterval (oddSteps w) (extraDepth w) u n := by
    rw [hmW]
    apply congrArg
      (fun hh : ℕ → ℕ =>
        profileDyadicCellInterval (oddSteps w) hh u n)
    funext k
    have hk := M.toPureBProfileObstruction_h_apply hL k
    dsimp [P] at hk ⊢
    simp only [MinimalActualABObstructionPacket.toPureBProfileObstruction_h_apply,
                parityExtraDepth, w]
  have hAttached :=
    A.straight_profileDyadicInterval_eq_threePow_mul_bracket hEnd
  dsimp only at hAttached
  rw [hProfile] at hAttached
  rw [hActual] at hAttached
  simpa [P, w, u] using hAttached

/--
上の actual specialization を criticalIntervalDefectZ form まで展開する。
-/
theorem integerFerrersDeficitInterval_eq_attached_intervalDefect_form
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth)
    (y : ℤ) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    (integerFerrersDeficitInterval w u n : ℤ) =
      (3 : ℤ) ^ (P.m - (u + n)) *
        (
          (2 : ℤ) ^ beattyIndex u *
              criticalIntervalDefectZ u (u + n) y +
            (2 : ℤ) ^ beattyIndex u *
              criticalIntervalGapZ u (u + n) * y -
            (2 : ℤ) ^ profileCheckpoint P.h u *
              ((3 : ℤ) ^ n - (2 : ℤ) ^ n)
        ) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let u := A.straightHenselStart + i
  have hBase :=
    integerFerrersDeficitInterval_eq_attached_straight_formula
      M hL A hEnd
  dsimp [P, u] at hBase ⊢
  rw [straightCheckpointFerrersBracketZ_eq_intervalDefect P.h u n y] at hBase
  exact hBase

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
