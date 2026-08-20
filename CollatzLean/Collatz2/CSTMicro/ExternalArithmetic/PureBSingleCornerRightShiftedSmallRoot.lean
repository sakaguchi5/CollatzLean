import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalPolylog

/-!
# Pure B: right shifted-critical small-root port

Stage 1--3 の第3段として導入したファイル名は `PureBSingleCornerRightShiftedSmallRoot`
のまま保持するが、この右側の数学そのものは single-corner 仮定を必要としない。

actual minimal B から得られる pure profile `P` には、single-corner geometry と無関係に
canonical terminal critical suffix

  [P.terminalCriticalStart, P.m)

が常に存在する。既存の `PureBTerminalPolylog` machinery はこの suffix に対してすでに

* terminal tail state の polynomial / dyadic size bound,
* critical record start の exact `BoundaryXiCandidate` 化,
* López--Stoll / Christoffel small-Xi precision bound,
* first-carry record の degree-14 length bound,
* suffix 全体の degree-210 polylog bound

を与えている。

したがって本ファイルの役割は、single-corner packet を仮定することではなく、
actual minimal B の canonical right suffix に既存 theorem を直接 specialize し、
後続の single-corner branch から利用しやすい right shifted-small-root port を公開することにある。

特に、このファイルの全 theorem は `|E(B)| = 1` より強い一般性を持ち、
任意の `MinimalActualABObstructionPacket` に対して成立する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
actual minimal B の canonical terminal critical start における tail state は、
`m + 1 ≤ 2^ell` の下で既存の uniform dyadic size bound を満たす。

この評価は single-corner 仮定を使用しない。
-/
theorem rightTailState_succ_le_dyadic
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    let P := M.toPureBProfileObstruction hL
    let T := P.terminalCriticalStart_spec
    P.terminalTailStateNat
        T (M.toPureBProfileObstruction_y_nonneg hL)
        P.terminalCriticalStart le_rfl T.1 + 1 ≤
      2 ^ (20 + 15 * ell) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have h :=
    terminalTailStateNat_succ_le_dyadic
      R P P.terminalCriticalStart_spec hy
      (le_rfl : P.terminalCriticalStart ≤ P.terminalCriticalStart)
      P.terminalCriticalStart_spec.1
      (by simpa [P] using hmSize)
  simpa [P] using h

/--
canonical terminal critical start `c = P.terminalCriticalStart` から
一つの critical record `[c,c+r)` が出るなら、その start tail state は
precision `beattyIndex r` の exact `BoundaryXiCandidate` になる。

これは right shifted-critical branch の small-root port であり、single-corner 仮定は不要。
-/
theorem rightRecordStart_isBoundaryXiCandidate
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {r : ℕ}
    (hend :
      (M.toPureBProfileObstruction hL).terminalCriticalStart + r ≤
        (M.toPureBProfileObstruction hL).m)
    (B :
      CriticalRecordPiece
        (M.toPureBProfileObstruction hL).terminalCriticalStart r) :
    let P := M.toPureBProfileObstruction hL
    let T := P.terminalCriticalStart_spec
    BoundaryXiCandidate
      (beattyIndex r)
      (P.terminalTailStateNat
        T (M.toPureBProfileObstruction_y_nonneg hL)
        P.terminalCriticalStart le_rfl T.1) := by
  dsimp
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hCandidate :=
    P.terminalRecordStart_isBoundaryXiCandidate
      P.terminalCriticalStart_spec hy
      (le_rfl : P.terminalCriticalStart ≤ P.terminalCriticalStart)
      (by simpa [P] using hend)
      (by simpa [P] using B)
  simpa [P] using hCandidate

/--
canonical right record の Beatty precision は、tail state の dyadic size と
既存 López--Stoll / Christoffel small-Xi theorem により
`smallXiPrecisionBound (20 + 15*ell)` 以下になる。

single-corner 固有の geometry はここでは使わない。
-/
theorem rightRecordPrecision_le
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {r ell : ℕ}
    (hend :
      (M.toPureBProfileObstruction hL).terminalCriticalStart + r ≤
        (M.toPureBProfileObstruction hL).m)
    (B :
      CriticalRecordPiece
        (M.toPureBProfileObstruction hL).terminalCriticalStart r)
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    beattyIndex r ≤ smallXiPrecisionBound (20 + 15 * ell) := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  let T : IsTerminalCriticalSuffix P P.terminalCriticalStart :=
    P.terminalCriticalStart_spec
  let x : ℕ :=
    P.terminalTailStateNat T hy
      P.terminalCriticalStart le_rfl T.1
  have hxSize : x + 1 ≤ 2 ^ (20 + 15 * ell) := by
    have h :=
      terminalTailStateNat_succ_le_dyadic
        R P T hy
        (le_rfl : P.terminalCriticalStart ≤ P.terminalCriticalStart)
        T.1
        (by simpa [P] using hmSize)
    simpa [x] using h
  have hCandidate : BoundaryXiCandidate (beattyIndex r) x := by
    have h :=
      P.terminalRecordStart_isBoundaryXiCandidate
        T hy
        (le_rfl : P.terminalCriticalStart ≤ P.terminalCriticalStart)
        (by simpa [P] using hend)
        (by simpa [P] using B)
    simpa [x] using h
  exact smallXiCandidate_precision_le R hxSize hCandidate

/--
canonical right suffix の first-carry record length は既存 degree-14 bound 以下。

この theorem も actual minimal B 一般に成立し、`|E(B)| = 1` は仮定しない。
-/
theorem rightRecord_length_le
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {r ell : ℕ}
    (hend :
      (M.toPureBProfileObstruction hL).terminalCriticalStart + r ≤
        (M.toPureBProfileObstruction hL).m)
    (B :
      CriticalRecordPiece
        (M.toPureBProfileObstruction hL).terminalCriticalStart r)
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell) :
    r ≤ terminalRecordLengthBound ell := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have h :=
    terminalRecordPiece_length_le
      R P P.terminalCriticalStart_spec hy
      (le_rfl : P.terminalCriticalStart ≤ P.terminalCriticalStart)
      (by simpa [P] using hend)
      (by simpa [P] using B)
      (by simpa [P] using hmSize)
  exact h

/--
actual minimal B の canonical terminal critical suffix 全体は、
既存 packing theorem により degree-210 polylog length を持つ。

これは right shifted-critical branch の global closure port であり、
single-corner branch に入る前から成立している一般 theorem の specialization である。
-/
theorem rightSuffix_le_log210
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).m -
        (M.toPureBProfileObstruction hL).terminalCriticalStart ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210 := by
  exact
    M.terminalCriticalSuffix_le_log210
      R hL (M.toPureBProfileObstruction hL).terminalCriticalStart_spec

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
