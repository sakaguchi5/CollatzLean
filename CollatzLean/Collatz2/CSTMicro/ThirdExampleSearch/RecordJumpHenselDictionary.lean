import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordFerrersProvenanceAdapter
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBeattyArithmetic

/-!
# 第3例探索 次段 5: Record jump と suffix Hensel staircase の exact dictionary

terminal straight component 上では、実 profile depth `P.h (b+i)` が
`suffixHenselDelta i` と exact に一致する。

従って本物の RecordFerrers provenance から作った `RecordJumpData` の boundary gap は、
仮定なしで Hensel delta そのものになる。

その上で既存 `suffixHenselDelta_step_dictionary` を輸送し、

* boundary gap 据え置き  <-> Beatty increment = 1
* boundary gap +1        <-> Beatty increment = 2

を Record jump の言葉で直接使えるようにする。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic
open MultiCorner

/--
terminal straight component では profile depth と restarted Hensel gap が exact に同じ。
-/
theorem suffixHenselDelta_eq_profileDepth
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i : ℕ}
    (hi : i < S.width) :
    S.suffixHenselDelta i = P.h (S.b + i) := by
  have hcEq := S.terminalCriticalStart_eq_b_add_width
  have hkC : S.b + i < P.terminalCriticalStart := by
    rw [hcEq]
    omega
  have hCheckpoint :=
    S.checkpoint_line
      (k := S.b + i)
      (by omega)
      hkC
  have hDiff : S.b + i - S.b = i := by omega
  have hCheckpoint' :
      beattyIndex (S.b + i) - P.h (S.b + i) =
        S.suffixHenselBase i := by
    simpa [profileCheckpoint, RestartedTerminalStraightPacket.suffixHenselBase,
      hDiff, Nat.add_assoc] using hCheckpoint
  have hLine :=
    singleCornerLine_lt_beatty
      (b := S.b) (n := i) S.beattyIndex_b_pos
  have hBaseLt :
      S.suffixHenselBase i < beattyIndex (S.b + i) := by
    simpa [RestartedTerminalStraightPacket.suffixHenselBase,
      Nat.add_assoc] using hLine
  have hcLeM :
      P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkLtM :
      S.b + i < P.m := by
    exact lt_of_lt_of_le hkC hcLeM
  have hDepthLe :
      P.h (S.b + i) ≤ beattyIndex (S.b + i) := by
    apply P.admissible.depth_le
    exact hkLtM
  unfold RestartedTerminalStraightPacket.suffixHenselDelta
  omega

/--
straight component の actual provenance boundary gap は suffix Hensel delta そのもの。
-/
theorem provenance_henselBoundaryGap_eq_suffixHenselDelta
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i : ℕ}
    (hi : i < S.width)
    (Q : MultiCorner.RecordFerrersCutProvenance P (S.b + i)) :
    (recordJumpDataOfProvenance Q).henselBoundaryGap =
      S.suffixHenselDelta i := by
  have hGap :=
    recordJumpDataOfProvenance_henselBoundaryGap_eq_profileDepth Q
  have hDelta := suffixHenselDelta_eq_profileDepth S hi
  exact hGap.trans hDelta.symm

/--
連続する二つの実 Record cuts について、boundary-gap step と Beatty step は exact に対応する。
-/
theorem recordFerrers_suffixHenselDelta_step_dictionary
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i : ℕ}
    (hi : i + 1 < S.width)
    (Q0 : MultiCorner.RecordFerrersCutProvenance P (S.b + i))
    (Q1 : MultiCorner.RecordFerrersCutProvenance P (S.b + (i + 1))) :
    ((recordJumpDataOfProvenance Q1).henselBoundaryGap =
        (recordJumpDataOfProvenance Q0).henselBoundaryGap ↔
      beattyIndex (S.b + i + 1) = beattyIndex (S.b + i) + 1) ∧
    ((recordJumpDataOfProvenance Q1).henselBoundaryGap =
        (recordJumpDataOfProvenance Q0).henselBoundaryGap + 1 ↔
      beattyIndex (S.b + i + 1) = beattyIndex (S.b + i) + 2) := by
  have hi0 : i < S.width := by omega
  have h0 :=
    provenance_henselBoundaryGap_eq_suffixHenselDelta S hi0 Q0
  have h1 :=
    provenance_henselBoundaryGap_eq_suffixHenselDelta S hi Q1
  rw [h0, h1]
  exact S.suffixHenselDelta_step_dictionary i

end ThirdExampleSearch
end CSTMicro
end Collatz2
