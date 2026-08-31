import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalThreeClearance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedIntervalFerrersHenselBridge

/-!
# Attached terminal: localized three-clearance

`AttachedTerminalThreeClearance` では global profile numerator

  N = profileDyadicCellNumerator P.m P.h

を第三の strict clearance として terminal balance に入れた後、
strict upper bound を作る段階では `N` を丸ごと捨てていた。

一方 Attached straight interval `[u,u+n)` には

  F_int = integerFerrersDeficitInterval w u n

という局所 Ferrers deficit があり、前段で actual profile の dyadic cell interval と
exact に同定されている。

本ファイルでは

1. 任意の profile interval dyadic mass は full numerator 以下、
2. actual Attached straight interval では `F_int <= N`、
3. 第三 clearance を `F_int + (N-F_int)` に exact に局所化、
4. `F_int` を捨てずに残した strengthened strict terminal bound、
5. 前段の Hensel endpoint normal form を代入した wrapper

を固定する。

中心となる strict bound は

  3^r (2^p E) + F_int
    < 3^r Psi(c) + 2^H deltaR + 3^(r+1) 2^p.

従って、これまで完全に捨てていた global profile numerator のうち、
選択した Attached interval の Ferrers deficit だけは terminal-side budget に
exact に残すことができる。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

/-! ## 1. profile interval は full numerator の部分和 -/

/--
profile の rank interval `[a,a+n)` の dyadic cell mass は、
full profile numerator 以下。

この補題には admissibility は不要で、単なる非負部分和の事実である。
-/
theorem profileDyadicCellInterval_le_fullNumerator
    (m : ℕ)
    (h : ℕ → ℕ)
    {a n : ℕ}
    (hRange : a + n ≤ m) :
    profileDyadicCellInterval m h a n ≤
      profileDyadicCellNumerator m h := by
  unfold profileDyadicCellInterval
    profileDyadicCellNumerator
    columnProfileSum
  let col : ℕ → ℕ := fun k =>
    Finset.sum (Finset.range (h k))
      (fun j => profileDyadicCellTerm m k j)
  change
    Finset.sum (Finset.range n) (fun t => col (a + t)) ≤
      Finset.sum (Finset.range m) col
  let r := m - (a + n)
  have hm : m = (a + n) + r := by
    dsimp [r]
    omega
  rw [hm]
  rw [Finset.sum_range_add]
  rw [Finset.sum_range_add]
  dsimp [col]
  omega

namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/-! ## 2. actual Attached interval: F_int <= N -/

/--
minimal actual B + Attached straight interval では integer Ferrers deficit は
pure profile の dyadic cell interval そのもの。

Nat equality として後段から直接使える形を公開する。
-/
theorem integerFerrersDeficitInterval_eq_attached_profileDyadicCellInterval
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    integerFerrersDeficitInterval w u n =
      profileDyadicCellInterval P.m P.h u n := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  let u := A.straightHenselStart + i
  have hFerrers :=
    integerFerrersDeficitInterval_eq_attached_straight_formula
      M hL A hEnd
  have hProfile :=
    A.straight_profileDyadicInterval_eq_threePow_mul_bracket hEnd
  dsimp [P, w, u] at hFerrers hProfile ⊢
  have hCast :
      (integerFerrersDeficitInterval w u n : ℤ) =
        (profileDyadicCellInterval P.m P.h u n : ℤ) := by
    exact hFerrers.trans hProfile.symm
  exact_mod_cast hCast

/--
Attached straight interval の integer Ferrers deficit は global profile numerator 以下。

  F_int[u,u+n) <= N.
-/
theorem integerFerrersDeficitInterval_le_profileDyadicCellNumerator
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    integerFerrersDeficitInterval w u n ≤
      profileDyadicCellNumerator P.m P.h := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  let u := A.straightHenselStart + i
  have hEq :=
    integerFerrersDeficitInterval_eq_attached_profileDyadicCellInterval
      M hL A hEnd
  dsimp [P, w, u] at hEq ⊢
  have hStartEnd := A.straightHenselStart_add_width
  have hStartEndP :
      A.straightHenselStart + A.straightHenselWidth =
        P.terminalCriticalStart := by
    simpa [P] using hStartEnd
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hRange : u + n ≤ P.m := by
    dsimp [u]
    omega
  rw [hEq]
  exact profileDyadicCellInterval_le_fullNumerator P.m P.h hRange

/-- Int 版。terminal balance へそのまま投入するための wrapper。 -/
theorem integerFerrersDeficitInterval_cast_le_profileDyadicCellNumerator
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    (integerFerrersDeficitInterval w u n : ℤ) ≤
      (profileDyadicCellNumerator P.m P.h : ℤ) := by
  dsimp
  have hNat :=
    integerFerrersDeficitInterval_le_profileDyadicCellNumerator
      M hL A hEnd
  exact_mod_cast hNat

/-! ## 3. third clearance の exact localization -/

/--
global third clearance `N` を、選択した Attached straight interval の deficit と
その非負 remainder に exact に分解した terminal balance。

  N = F_int + (N - F_int)

なので、元の three-clearance exact balance の情報は一切失わない。
-/
theorem terminalCarryRhs_localizedThreeClearance_exact_balance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let D := S.toFareyCellPacket.residue
    let G := S.toFareyCellPacket.G
    let r := S.fareyRightExponent
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    let F := integerFerrersDeficitInterval w u n
    let N := profileDyadicCellNumerator P.m P.h
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) +
      (2 : ℤ) ^ S.length * (G - D) +
      (3 : ℤ) ^ P.m *
        ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) +
      (F : ℤ) +
      ((N - F : ℕ) : ℤ) =
      (3 : ℤ) ^ r *
          criticalPrefixPhiZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  let w := exponentWordOfParity M.word
  let u := A.straightHenselStart + i
  let F := integerFerrersDeficitInterval w u n
  let N := profileDyadicCellNumerator P.m P.h
  have hBal :=
    A.terminalCarryRhs_threeClearance_exact_balance M hL T
  have hLe :=
    integerFerrersDeficitInterval_le_profileDyadicCellNumerator
      M hL A hEnd
  dsimp [P, S, w, u, F, N] at hBal hLe ⊢
  have hSplitNat :
      integerFerrersDeficitInterval w u n +
          (profileDyadicCellNumerator P.m P.h -
            integerFerrersDeficitInterval w u n) =
        profileDyadicCellNumerator P.m P.h := by
    simpa [P, w, u] using Nat.add_sub_of_le hLe
  have hSplitZ :
      (integerFerrersDeficitInterval w u n : ℤ) +
          ((profileDyadicCellNumerator P.m P.h -
            integerFerrersDeficitInterval w u n : ℕ) : ℤ) =
        (profileDyadicCellNumerator P.m P.h : ℤ) := by
    exact_mod_cast hSplitNat
  calc
    (3 : ℤ) ^ T.step.edge.fareyRightExponent *
          ((2 : ℤ) ^ T.step.edge.position * A.terminalCarryRhs) +
        (2 : ℤ) ^ T.step.edge.length *
          (T.step.edge.toFareyCellPacket.G -
            T.step.edge.toFareyCellPacket.residue) +
        (3 : ℤ) ^ (M.toPureBProfileObstruction hL).m *
          ((T.step.edge.deltaR : ℤ) -
            (leastRepresentative M.word : ℤ)) +
        (integerFerrersDeficitInterval w u n : ℤ) +
        ((profileDyadicCellNumerator P.m P.h -
          integerFerrersDeficitInterval w u n : ℕ) : ℤ)
        =
      (3 : ℤ) ^ T.step.edge.fareyRightExponent *
          ((2 : ℤ) ^ T.step.edge.position * A.terminalCarryRhs) +
        (2 : ℤ) ^ T.step.edge.length *
          (T.step.edge.toFareyCellPacket.G -
            T.step.edge.toFareyCellPacket.residue) +
        (3 : ℤ) ^ (M.toPureBProfileObstruction hL).m *
          ((T.step.edge.deltaR : ℤ) -
            (leastRepresentative M.word : ℤ)) +
        (profileDyadicCellNumerator P.m P.h : ℤ) := by
          rw [← hSplitZ]
          ring
    _ =
      (3 : ℤ) ^ T.step.edge.fareyRightExponent *
          criticalPrefixPhiZ
            (M.toPureBProfileObstruction hL).terminalCriticalStart +
        (2 : ℤ) ^ T.step.edge.length *
          (T.step.edge.deltaR : ℤ) +
        (3 : ℤ) ^ (T.step.edge.fareyRightExponent + 1) *
          (2 : ℤ) ^ T.step.edge.position := by
            simpa [P] using hBal

/-! ## 4. localized strengthened strict bound -/

/--
third clearance のうち selected interval deficit `F_int` は捨てず、
残りの strict-positive Farey / representative clearances だけを捨てる。

  3^r (2^p E) + F_int
    < 3^r Psi(c) + 2^H deltaR + 3^(r+1) 2^p.

`N > 0` は不要で、二つの terminal strict clearances と `F_int <= N` だけで成立する。
従って `hStart > 0` もこの theorem 自体には不要。
-/
theorem terminalCarryRhs_add_integerFerrersDeficitInterval_strict_lt_farey_criticalPrefix_budget
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let r := S.fareyRightExponent
    let w := exponentWordOfParity M.word
    let u := A.straightHenselStart + i
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) +
      (integerFerrersDeficitInterval w u n : ℤ) <
      (3 : ℤ) ^ r *
          criticalPrefixPhiZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  let w := exponentWordOfParity M.word
  let u := A.straightHenselStart + i
  have hBal :=
    A.terminalCarryRhs_threeClearance_exact_balance M hL T
  have hLe :=
    integerFerrersDeficitInterval_cast_le_profileDyadicCellNumerator
      M hL A hEnd
  have hPos := terminalTop_twoClearances_pos M hL T
  have hGapPos :
      0 <
        (2 : ℤ) ^ S.length *
          (S.toFareyCellPacket.G - S.toFareyCellPacket.residue) :=
    mul_pos (by positivity) hPos.1
  have hRPos :
      0 <
        (3 : ℤ) ^ P.m *
          ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) :=
    mul_pos (by positivity) hPos.2
  dsimp [P, S, w, u] at hBal hLe hGapPos hRPos ⊢
  linarith

/-! ## 5. Hensel endpoint normal form を代入した localized bound -/

/--
前段の exact identification

  F_int
    = 3^(m-b) * 2^checkpoint(a)
        * (3^p q_i - 2^p q_j)

を localized three-clearance bound に代入する。

これが次段で terminal-near anchor budget と直接比較する形である。
-/
theorem terminalCarryRhs_add_henselQEndpointFerrersTerm_strict_lt_farey_criticalPrefix_budget
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {i j Delta : ℕ}
    (hij : i < j)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let r := S.fareyRightExponent
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let p := j - i
    let a := A.straightHenselStart + i
    let b := A.straightHenselStart + j
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) +
      (3 : ℤ) ^ (P.m - b) *
        (2 : ℤ) ^ profileCheckpoint P.h a *
          ((3 : ℤ) ^ p * C.q i -
            (2 : ℤ) ^ p * C.q j) <
      (3 : ℤ) ^ r *
          criticalPrefixPhiZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let p := j - i
  let a := A.straightHenselStart + i
  let b := A.straightHenselStart + j
  have hEnd : i + p ≤ A.straightHenselWidth := by
    dsimp [p]
    omega
  have hLocal :=
    terminalCarryRhs_add_integerFerrersDeficitInterval_strict_lt_farey_criticalPrefix_budget
      M hL A T hEnd
  have hFerrers :=
    integerFerrersDeficitInterval_eq_henselQEndpoints
      M hL A hStart
      (i := i)
      (j := j)
      (Delta := Delta)
      hij
      hj
      hDelta
  dsimp [P, S, C, p, a, b] at hLocal hFerrers ⊢
  rw [hFerrers] at hLocal
  exact hLocal

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
