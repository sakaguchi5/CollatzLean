import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalFareyComparison
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftOfCriticalizationBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreValuation
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileDefectBridge

set_option linter.style.longLine false

/-!
# Attached terminal state と criticalization unit の exact bridge

`c = terminalCriticalStart`, `s = criticalizationStart` とする。

前段では attached terminal/Farey 比較の右辺に

  profileAffineLocalPrefixZ c

が残っていた。一方 extra-left 側では global profile numerator の最初の
nonzero 3-adic digit として

  criticalizationUnit

を保持している。

このファイルでは両者を terminal noncritical core を介して exact に接続する。

1. global profile numerator の二つの factorization を比較して

     terminalCore = 3^(c-s) * criticalizationUnit

   を得る。

2. cut `c` まで admissible profile を restriction し、既存の

     affineNumerator + profileNumerator = criticalPrefix

   を使って

     localPrefix(c) + terminalCore = Psi(c)

   を得る。

3. 1 と 2 を合成して

     localPrefix(c) = Psi(c) - 3^(c-s) * criticalizationUnit

   と local prefix を消去する。

4. actual minimal B では `y-q = leastRepresentative M.word` なので、
   terminal integral critical state `Z_c` まで戻して

     2^beta(c) Z_c + 3^(c-s) U
       = Psi(c) + 3^c R

   という exact unit-state gluing を得る。

ここでは inequality や `lowerR` は導入しない。
目的は attached branch と extra-left branch が共有する arithmetic spine を
等式だけで固定することである。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-! ## 1. terminal core = scaled criticalization unit -/

/--
Global profile numerator の

  N = 3^(m-c) * terminalCore
  N = 3^(m-s) * criticalizationUnit

という二つの exact factorization から共通因子 `3^(m-c)` を消す。
-/
theorem terminalCore_eq_threePow_mul_criticalizationUnit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      (3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart) *
        criticalizationUnit P hStart := by
  have hsLe :
      P.criticalizationStart ≤ P.terminalCriticalStart :=
    P.criticalizationStart_le_terminalCriticalStart
  have hcLe :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hCore :=
    P.profileNumerator_cast_eq_threePow_mul_terminalCore
  have hUnit :=
    profileNumerator_eq_threePow_mul_criticalizationUnit P hStart
  have hExp :
      P.m - P.criticalizationStart =
        (P.m - P.terminalCriticalStart) +
          (P.terminalCriticalStart - P.criticalizationStart) := by
    omega
  rw [hExp, pow_add] at hUnit
  have hEq :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ) =
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          ((3 : ℤ) ^
              (P.terminalCriticalStart - P.criticalizationStart) *
            criticalizationUnit P hStart) := by
    calc
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ)
          = (profileDyadicCellNumerator P.m P.h : ℤ) :=
            hCore.symm
      _ =
          ((3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
              (3 : ℤ) ^
                (P.terminalCriticalStart - P.criticalizationStart)) *
            criticalizationUnit P hStart := hUnit
      _ =
          (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
            ((3 : ℤ) ^
                (P.terminalCriticalStart - P.criticalizationStart) *
              criticalizationUnit P hStart) := by
            ring
  have hPowNe :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) ≠ 0 := by
    positivity
  exact mul_left_cancel₀ hPowNe hEq

/-! ## 2. local affine prefix と terminal core の exact complement -/

/--
`P.admissible` を terminal critical start `c` まで restriction する。

後続の complement identity で generic profile theorem を `m=c` として使うための
薄い wrapper である。
-/
theorem admissibleSturmianProfile_terminalCriticalStart
    (P : PureBProfileObstruction) :
    AdmissibleSturmianProfile P.terminalCriticalStart P.h := by
  have hcLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  constructor
  · intro k hk
    exact P.admissible.1 k (lt_of_lt_of_le hk hcLe)
  · intro k hk
    exact P.admissible.2 k (lt_of_lt_of_le hk hcLe)

/--
terminal local prefix は `m=c` の ordinary profile affine numerator の Int cast。
-/
theorem profileAffineLocalPrefixZ_eq_profileAffineNumerator_cast_terminal
    (P : PureBProfileObstruction) :
    P.profileAffineLocalPrefixZ P.terminalCriticalStart =
      (profileAffineNumerator P.terminalCriticalStart P.h : ℤ) := by
  unfold PureBProfileObstruction.profileAffineLocalPrefixZ
  unfold profileAffineNumerator
  push_cast
  rfl

/--
terminal noncritical core は `m=c` の profile dyadic cell numerator の Int cast。
-/
theorem terminalCore_cast_eq_profileDyadicCellNumerator_terminal
    (P : PureBProfileObstruction) :
    (P.terminalNoncriticalProfileCore : ℤ) =
      (profileDyadicCellNumerator P.terminalCriticalStart P.h : ℤ) := by
  have hClosed :=
    profileDyadicCellNumerator_eq_closed
      (admissibleSturmianProfile_terminalCriticalStart P)
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hClosed
  unfold PureBProfileObstruction.terminalNoncriticalProfileCore
  exact hCast.symm

/--
terminal critical start `c` で、actual checkpoint affine prefix と removed profile mass は
critical Beatty prefixを exact に分割する。

  localPrefix(c) + terminalCore = Psi(c).
-/
theorem profileAffineLocalPrefixZ_add_terminalCore_eq_criticalPrefixPhiZ
    (P : PureBProfileObstruction) :
    P.profileAffineLocalPrefixZ P.terminalCriticalStart +
        (P.terminalNoncriticalProfileCore : ℤ) =
      criticalPrefixPhiZ P.terminalCriticalStart := by
  have hAdmissible :=
    admissibleSturmianProfile_terminalCriticalStart P
  have hComplement :=
    profileAffineNumerator_cast_eq_criticalPrefixPhiZ_sub_profileDyadic
      hAdmissible
  rw [profileAffineLocalPrefixZ_eq_profileAffineNumerator_cast_terminal P]
  rw [terminalCore_cast_eq_profileDyadicCellNumerator_terminal P]
  linarith

/-! ## 3. local prefix を criticalization unit で消去 -/

/--
terminal core を criticalization unit で置き換えることで、
attached terminal/Farey comparison に残っていた local prefix を exact に消去する。
-/
theorem profileAffineLocalPrefixZ_eq_criticalPrefixPhiZ_sub_scaledCriticalizationUnit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    P.profileAffineLocalPrefixZ P.terminalCriticalStart =
      criticalPrefixPhiZ P.terminalCriticalStart -
        (3 : ℤ) ^
            (P.terminalCriticalStart - P.criticalizationStart) *
          criticalizationUnit P hStart := by
  have hComplement :=
    profileAffineLocalPrefixZ_add_terminalCore_eq_criticalPrefixPhiZ P
  have hCore :=
    terminalCore_eq_threePow_mul_criticalizationUnit P hStart
  rw [hCore] at hComplement
  linarith

/-! ## 4. actual minimal B: unit と terminal critical state の exact gluing -/

/--
actual minimal B に対する本命の unit-state bridge。

`c = terminalCriticalStart`, `s = criticalizationStart`,
`U = criticalizationUnit`, `R = leastRepresentative M.word` とすると

  2^beta(c) Z_c + 3^(c-s) U
    = Psi(c) + 3^c R.

左辺は attached critical/Hensel state と extra-left 3-adic unit、
右辺は critical Beatty prefix と actual minimal representative だけからなる。
-/
theorem actualTerminalCriticalState_scaled_add_scaledCriticalizationUnit_eq_criticalPrefix_add_representative
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    let P := M.toPureBProfileObstruction hL
    let c := P.terminalCriticalStart
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I c
        P.criticalizationStart_le_terminalCriticalStart
        P.terminalCriticalStart_spec.1
    (2 : ℤ) ^ beattyIndex c * Z +
        (3 : ℤ) ^ (c - P.criticalizationStart) *
          criticalizationUnit P hStart =
      criticalPrefixPhiZ c +
        (3 : ℤ) ^ c * (leastRepresentative M.word : ℤ) := by
  dsimp only
  let P := M.toPureBProfileObstruction hL
  have hStartP : 0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hState :=
    P.terminalCritical_integralState_scaled_eq_localPrefix_add_y_sub_q
  have hLocal :=
    profileAffineLocalPrefixZ_eq_criticalPrefixPhiZ_sub_scaledCriticalizationUnit
      P hStartP
  have hRepresentative :=
    M.toPureBProfileObstruction_y_sub_q_eq_leastRepresentative hL
  dsimp [P] at hState hLocal hRepresentative ⊢
  rw [hLocal, hRepresentative] at hState
  linarith

end MultiCorner
end CSTMicro
end Collatz2
