import CollatzLean.CollatzSecondLayer.InfiniteBranches

/-!
# 深さ非有界な特殊C3部分列

有限SpecialC3 packet一個の存在ではなく、同一の無限解析列から抽出され、
first-carry深さが任意に大きくなる特殊C3部分列を最終障害として定義する。

C3排除定理が否定すべき対象は `HasArbitrarilyDeepSpecialC3` である。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 一つの特殊C3項だけを保存する有限snapshot。 -/
structure SpecialC3Data where
  sourceCylinder : CanonicalC3Witness
  terminalPair : TerminalPairData
  sourceRelation :
    terminalPair.A ++ terminalPair.R = sourceCylinder.word
  sourceStart : terminalPair.X = sourceCylinder.start
  sourceFinish : terminalPair.YAR = sourceCylinder.finish
  carry : CarryComparison
  carryOrigin : CarryOrigin terminalPair carry
  deferredCarry : DeferredCarry carry
  shadow : CanonicalShadowData terminalPair.R
  negativeShadow : shadow.shadow < 0
  changingCenter :
    center terminalPair.A ≠ center terminalPair.R

namespace SpecialC3At

/-- 無限解析列中の特殊C3項から有限snapshotを切り出す。 -/
def snapshot
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    {n : ℕ}
    {P : TerminalAnalysisPacket E n}
    (H : SpecialC3At P) : SpecialC3Data where
  sourceCylinder := P.sourceCylinder
  terminalPair := P.criticalPair
  sourceRelation := P.sourceRelation
  sourceStart := P.sourceStart
  sourceFinish := P.sourceFinish
  carry := P.carry
  carryOrigin := P.carryOrigin
  deferredCarry := H.deferredCarry
  shadow := P.shadow
  negativeShadow := H.negativeShadow
  changingCenter := H.changingCenter

end SpecialC3At

/--
特殊C3項が一つの無限解析列から狭義単調な部分列として抽出され、
そのfirst-carry深さが無限大へ進むこと。
-/
structure ArbitrarilyDeepSpecialC3Data
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {E : InfiniteTerminalExtraction S}
    (A : InfiniteTerminalAnalysis E) where
  select : Subsequence
  special : ∀ n : ℕ,
    SpecialC3At (A.packet (select.index n))
  depths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (A.packet (select.index j)).carry.d

/-- 深さが任意に大きい特殊C3部分列が存在すること。 -/
def HasArbitrarilyDeepSpecialC3 : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ E : InfiniteTerminalExtraction S,
  ∃ A : InfiniteTerminalAnalysis E,
    Nonempty (ArbitrarilyDeepSpecialC3Data A)

/--
第三bridge。

各無限terminal抽出から、深さ非有界な解析packet列を構成し、
閉じる出口が無限部分列上で持続するか、深さ非有界な特殊C3部分列へ送る。
無限鳩の巣、deep extraction、first-carry深さ保存をここへ集約する。
-/
def InfiniteTerminalAnalysisPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ E : InfiniteTerminalExtraction S,
    ∃ A : InfiniteTerminalAnalysis E,
      Nonempty (PersistentAlternativeExitData A) ∨
      Nonempty (ArbitrarilyDeepSpecialC3Data A)

/-- C3排除側が最終的に証明すべき命題。 -/
def AsymptoticSpecialC3ExclusionPrinciple : Prop :=
  ¬ HasArbitrarilyDeepSpecialC3

end CollatzSecondLayer
