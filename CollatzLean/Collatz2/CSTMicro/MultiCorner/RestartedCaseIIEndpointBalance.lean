import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalAffineNumerator
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitStartState
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ShiftedCriticalizationHenselPacket
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalCoreValuation

/-!
# Case II endpoint `s=c`: zero-width Hensel の exact affine balance

`s < c` では shifted Hensel quotient が正になる。
一方 `s = c` では shifted width が 0 なので、その quotient を使ってはいけない。

しかし `s=c` では別の exact cancellation がある。
criticalization unit と terminal noncritical core は、同じ global profile numerator を
同じ `3^(m-c)` で割った quotient なので一致する。

これを criticalization start-state identity と

  criticalPrefix = affineNumerator + closedNumerator

へ代入すると、closed numerator が消えて

  3^c (y-q) + A_c = 2^beta(c) Z_c

を得る。

さらに restarted interval `[b,c)` の relative affine transport と合わせると

  2^beta(c) Z_c + 2^(beta(b)-1+width)
    = 3^c (y-q) + 3^width * affineSeed

となる。
これは `s=c` branch で失われた正幅 Hensel quotient の代わりになる exact identity である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
`criticalizationStart = terminalCriticalStart` なら、criticalization unit は
terminal noncritical core そのもの。
-/
theorem criticalizationUnit_eq_terminalCore_of_start_eq_terminal
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    criticalizationUnit P hStart =
      (P.terminalNoncriticalProfileCore : ℤ) := by
  have hUnit :=
    profileNumerator_eq_threePow_mul_criticalizationUnit P hStart
  have hCore :=
    P.profileNumerator_cast_eq_threePow_mul_terminalCore
  rw [hsEq] at hUnit
  have hPowNe :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) ≠ 0 := by
    positivity
  have hScaled :
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          criticalizationUnit P hStart =
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ) := by
    calc
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          criticalizationUnit P hStart =
        (profileDyadicCellNumerator P.m P.h : ℤ) := hUnit.symm
      _ =
        (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
          (P.terminalNoncriticalProfileCore : ℤ) := hCore
  exact mul_left_cancel₀ hPowNe hScaled

/--
`s=c` endpoint の exact affine balance。

shifted quotient を作らず、zero-width cancellation を直接行う。
-/
theorem caseIIEndpoint_exactAffineBalance
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    (3 : ℤ) ^ P.criticalizationStart *
          (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.criticalizationStart P.h : ℤ) =
      (2 : ℤ) ^ beattyIndex P.criticalizationStart *
        P.criticalizationStartStateInt := by
  have hUnitCore :=
    criticalizationUnit_eq_terminalCore_of_start_eq_terminal
      P hStart hsEq
  have hCoreAtStart :
      criticalizationUnit P hStart =
        (profileDyadicClosedNumerator
          P.criticalizationStart P.h : ℤ) := by
    calc
      criticalizationUnit P hStart =
          (P.terminalNoncriticalProfileCore : ℤ) := hUnitCore
      _ =
          (profileDyadicClosedNumerator
            P.criticalizationStart P.h : ℤ) := by
              simp [PureBProfileObstruction.terminalNoncriticalProfileCore, hsEq]
  have hState :=
    criticalizationUnit_eq_start_state_expression P hStart
  have hPrefix :
      (profileAffineNumerator P.criticalizationStart P.h : ℤ) +
          (profileDyadicClosedNumerator
            P.criticalizationStart P.h : ℤ) =
        criticalPrefixPhiZ P.criticalizationStart :=
    ShiftedCriticalizationHenselPacket.startAffine_add_startClosed_eq_criticalPrefix
  rw [hCoreAtStart, ← hPrefix] at hState
  linarith

namespace RestartedTerminalGeometryPacket

/--
restarted geometry の `c` で書いた `s=c` exact affine balance。
-/
theorem caseIIEndpoint_exactAffineBalance
    {P : PureBProfileObstruction}
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) +
        (profileAffineNumerator P.terminalCriticalStart P.h : ℤ) =
      (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
        P.criticalizationStartStateInt := by
  have h :=
    Collatz2.CSTMicro.MultiCorner.caseIIEndpoint_exactAffineBalance
      P hStart hsEq
  simpa [hsEq] using h

/--
`s=c` endpoint balance と `[b,c)` relative affine transport を合成した exact identity。

右端 state と左端 affine seed が、同じ式の中に初めて現れる。
-/
theorem caseIIEndpoint_restartedSeedBalance
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.criticalizationStartStateInt +
        (2 : ℤ) ^ (beattyIndex S.b - 1 + S.width) =
      (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) +
        (3 : ℤ) ^ S.width * (S.affineSeed : ℤ) := by
  have hEndpoint :=
    caseIIEndpoint_exactAffineBalance hStart hsEq
  have hTransport :=
    S.affineEndpointMass_cast_eq_threePow_mul_affineSeed
  push_cast at hTransport
  linarith

/--
`s=c` endpoint の surplus を difference 形で exact に書く。

  stateMass + boundaryMass - globalTerm = 3^width * affineSeed.
-/
theorem caseIIEndpoint_surplus_eq_threePow_mul_affineSeed
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.criticalizationStartStateInt +
        (2 : ℤ) ^ (beattyIndex S.b - 1 + S.width) -
        (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) =
      (3 : ℤ) ^ S.width * (S.affineSeed : ℤ) := by
  have hBalance :=
    S.caseIIEndpoint_restartedSeedBalance hStart hsEq
  linarith

/-- `s=c` endpoint surplus は strict positive。 -/
theorem caseIIEndpoint_surplus_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    0 <
      (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.criticalizationStartStateInt +
        (2 : ℤ) ^ (beattyIndex S.b - 1 + S.width) -
        (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ)) := by
  rw [S.caseIIEndpoint_surplus_eq_threePow_mul_affineSeed hStart hsEq]
  have hSeedNat : 0 < S.affineSeed := S.affineSeed_pos
  have hSeed : (0 : ℤ) < (S.affineSeed : ℤ) := by
    exact_mod_cast hSeedNat
  exact mul_pos (by positivity) hSeed

/--
上の exact identity の affine seed 項は strict positive。
従って endpoint state 側には strict な余剰が残る。
-/
theorem caseIIEndpoint_globalTerm_lt_state_add_boundaryMass
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hsEq :
      P.criticalizationStart = P.terminalCriticalStart) :
    (3 : ℤ) ^ P.terminalCriticalStart *
        (P.y - (P.q : ℤ)) <
      (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.criticalizationStartStateInt +
        (2 : ℤ) ^ (beattyIndex S.b - 1 + S.width) := by
  have hBalance :=
    S.caseIIEndpoint_restartedSeedBalance hStart hsEq
  have hSeedNat : 0 < S.affineSeed := S.affineSeed_pos
  have hSeed : (0 : ℤ) < (S.affineSeed : ℤ) := by
    exact_mod_cast hSeedNat
  have hPow : (0 : ℤ) < (3 : ℤ) ^ S.width := by
    positivity
  have hPos :
      0 < (3 : ℤ) ^ S.width * (S.affineSeed : ℤ) :=
    mul_pos hPow hSeed
  linarith

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
