import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalizationUnitBridge

/-!
# Attached terminal: three-clearance exact balance

前段 `AttachedTerminalFareyComparison` では terminal fused RHS に対して

  2^H (G-D),
  3^m (deltaR-R)

という二つの strict clearance を得たが、右辺には

  3^r * profileAffineLocalPrefixZ c

が残っていた。

`AttachedCriticalizationUnitBridge` により

  localPrefix(c) + terminalCore = Psi(c)

が exact に得られ、さらに global profile numerator は

  N = 3^(m-c) * terminalCore

である。terminal Farey decomposition の `m = c+r` を使えば

  3^r * localPrefix(c) + N = 3^r * Psi(c)

となる。

従って two-clearance balance に global profile numerator `N` を第三の clearance
として exact に移項できる。

このファイルでは

1. scaled local-prefix complement,
2. positive criticalization start から `N > 0`,
3. three-clearance exact balance,
4. 三つの clearance の同時 positivity,
5. localPrefix を含まない strengthened strict bound

までを theorem として固定する。

right-end smallness `|M_m| < 3^m` 自体はここではまだ主張しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-! ## 1. local prefix と global profile numerator の scaled complement -/

/--
terminal critical start `c` での complement identity を global terminal lengthまで
3-power で持ち上げる。

  3^(m-c) localPrefix(c) + N
    = 3^(m-c) Psi(c).

ここでは criticalization start の positivity は不要である。
-/
theorem profileAffineLocalPrefixZ_scaled_add_profileNumerator_eq_scaled_criticalPrefixPhiZ
    (P : PureBProfileObstruction) :
    (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
        P.profileAffineLocalPrefixZ P.terminalCriticalStart +
      (profileDyadicCellNumerator P.m P.h : ℤ) =
    (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
      criticalPrefixPhiZ P.terminalCriticalStart := by
  have hComplement :=
    profileAffineLocalPrefixZ_add_terminalCore_eq_criticalPrefixPhiZ P
  have hCore :=
    P.profileNumerator_cast_eq_threePow_mul_terminalCore
  rw [hCore]
  calc
    (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ)
        =
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
        (P.profileAffineLocalPrefixZ P.terminalCriticalStart +
          (P.terminalNoncriticalProfileCore : ℤ)) := by
            ring
    _ =
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
        criticalPrefixPhiZ P.terminalCriticalStart := by
          rw [hComplement]

/-! ## 2. positive criticalization start なら global profile numerator は strict positive -/

/--
positive criticalization start では profile numerator の exact 3-adic order が有限であり、
従って Nat-valued global profile numerator は zero ではない。

  0 < N.
-/
theorem profileDyadicCellNumerator_pos_of_criticalizationStart_pos
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    0 < profileDyadicCellNumerator P.m P.h := by
  have hExact :=
    P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  by_contra hNotPos
  have hZero : profileDyadicCellNumerator P.m P.h = 0 := by
    omega
  apply hExact.2
  simp [hZero]

/-- Int cast した global profile numerator も strict positive。 -/
theorem profileDyadicCellNumerator_cast_pos_of_criticalizationStart_pos
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    0 < (profileDyadicCellNumerator P.m P.h : ℤ) := by
  have hPos :=
    profileDyadicCellNumerator_pos_of_criticalizationStart_pos P hStart
  exact_mod_cast hPos

namespace AttachedTwoCornerPacket

/-! ## 3. terminal three-clearance exact balance -/

/--
terminal two-clearance balance の local-prefix budget を global profile numeratorで
exact に補完する。

`c = terminalCriticalStart`, `r = fareyRightExponent` とすると `m = c+r` なので

  3^r localPrefix(c) + N = 3^r Psi(c).

従って

  3^r (2^p E)
    + 2^H (G-D)
    + 3^m (deltaR-R)
    + N
  =
    3^r Psi(c)
    + 2^H deltaR
    + 3^(r+1) 2^p.

これは `hStart > 0` を仮定しない exact identity である。
-/
theorem terminalCarryRhs_threeClearance_exact_balance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let D := S.toFareyCellPacket.residue
    let G := S.toFareyCellPacket.G
    let r := S.fareyRightExponent
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) +
      (2 : ℤ) ^ S.length * (G - D) +
      (3 : ℤ) ^ P.m *
        ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) +
      (profileDyadicCellNumerator P.m P.h : ℤ) =
      (3 : ℤ) ^ r *
          criticalPrefixPhiZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  have hBal :=
    terminalCarryRhs_twoClearance_exact_balance M hL A T
  have hScaled :=
    profileAffineLocalPrefixZ_scaled_add_profileNumerator_eq_scaled_criticalPrefixPhiZ P
  have hOdd := S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent
  have hA := T.fareyLeftExponent_eq
  have hM := T.oddTotal_eq
  have hm :
      P.m = P.terminalCriticalStart + S.fareyRightExponent := by
    dsimp [P, S] at hOdd hA hM ⊢
    rw [hM, hA] at hOdd
    exact hOdd
  have hDiff :
      P.m - P.terminalCriticalStart = S.fareyRightExponent := by
    omega
  rw [hDiff] at hScaled
  dsimp [P, S] at hBal hScaled ⊢
  linear_combination hBal + hScaled

/-! ## 4. 三つの terminal clearance は同時に strict positive -/

/--
terminal minimality の二つの strict clearance に、positive criticalization startから来る
strict positive global profile numerator を加える。
-/
theorem terminalTop_threeClearances_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    let P := M.toPureBProfileObstruction hL
    0 < T.step.edge.toFareyCellPacket.G -
        T.step.edge.toFareyCellPacket.residue ∧
      0 < (T.step.edge.deltaR : ℤ) -
        (leastRepresentative M.word : ℤ) ∧
      0 < (profileDyadicCellNumerator P.m P.h : ℤ) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  have hStartP : 0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hTwo := terminalTop_twoClearances_pos M hL T
  have hN :=
    profileDyadicCellNumerator_cast_pos_of_criticalizationStart_pos P hStartP
  dsimp [P] at hN ⊢
  exact ⟨hTwo.1, hTwo.2, hN⟩

/-! ## 5. localPrefix-free strengthened strict bound -/

/--
three-clearance exact balance から三つの strict positive term

  2^H (G-D),
  3^m (deltaR-R),
  N

を捨てて得る strengthened terminal bound。

前段の bound と異なり、右辺には `profileAffineLocalPrefixZ c` が残らない。

  3^r (2^p E)
    < 3^r Psi(c) + 2^H deltaR + 3^(r+1)2^p.

これが right-end smallness へ渡す pure critical/Farey budget である。
-/
theorem terminalCarryRhs_strict_lt_farey_criticalPrefix_budget
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (T :
      MinimalActualABObstructionPacket.TerminalTopCellMinimalityPacket
        M hL)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    let P := M.toPureBProfileObstruction hL
    let S := T.step.edge
    let r := S.fareyRightExponent
    (3 : ℤ) ^ r *
        ((2 : ℤ) ^ S.position * A.terminalCarryRhs) <
      (3 : ℤ) ^ r *
          criticalPrefixPhiZ P.terminalCriticalStart +
        (2 : ℤ) ^ S.length * (S.deltaR : ℤ) +
        (3 : ℤ) ^ (r + 1) * (2 : ℤ) ^ S.position := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  let S := T.step.edge
  have hBal :=
    terminalCarryRhs_threeClearance_exact_balance M hL A T
  have hPos :=
    terminalTop_threeClearances_pos M hL T hStart
  have hGapPos :
      0 <
        (2 : ℤ) ^ S.length *
          (S.toFareyCellPacket.G - S.toFareyCellPacket.residue) :=
    mul_pos (by positivity) hPos.1
  have hRPos :
      0 <
        (3 : ℤ) ^ P.m *
          ((S.deltaR : ℤ) - (leastRepresentative M.word : ℤ)) :=
    mul_pos (by positivity) hPos.2.1
  have hNPos :
      0 < (profileDyadicCellNumerator P.m P.h : ℤ) := by
    simpa [P] using hPos.2.2
  dsimp [P, S] at hBal hGapPos hRPos hNPos ⊢
  linarith

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
