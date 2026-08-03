import CollatzLean.CollatzSecondLayer.InfiniteBranches

/-!
# 深さ非有界な修正後Special C3部分列

Special C3は、最小非負canonical終点をnegative shadowと誤認する旧定義を廃止する。
修正後は、suffix開始値がcanonical境界（replay quotient 0）にあり、一つ下の
合同代表に対応するpredecessor shadowが負で、first-carryがdeferredとなる項を
保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 一つの修正後Special C3項だけを保存する有限snapshot。 -/
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
  replay :
    CanonicalReplayCoordinate
      terminalPair.R terminalPair.YA terminalPair.YAR
  canonicalBoundary : replay.quotient = 0
  negativePredecessorShadow :
    predecessorShadow terminalPair.R < 0

namespace SpecialC3Data

/-- Special C3 snapshotが持つconnection方程式。 -/
theorem connectionEquation (D : SpecialC3Data) :
    (D.terminalPair.YAR : ℤ) -
        predecessorShadow D.terminalPair.R =
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R := by
  have h := D.replay.connectionEquation
  rw [D.canonicalBoundary] at h
  simpa using h

/-- negative predecessor shadowの大きさをexactに表す。 -/
theorem negativeShadowExact (D : SpecialC3Data) :
    - predecessorShadow D.terminalPair.R =
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R -
        (D.terminalPair.YAR : ℤ) := by
  have h := D.connectionEquation
  linear_combination h

/-- Special C3では実終点は`2*3^q`より小さい。 -/
theorem finish_lt_two_mul_threePow (D : SpecialC3Data) :
    (D.terminalPair.YAR : ℤ) <
      2 * (3 : ℤ) ^ oddSteps D.terminalPair.R := by
  have h := D.connectionEquation
  have hneg := D.negativePredecessorShadow
  omega

/-- canonical境界ではsuffix開始値はcanonical最小非負代表そのもの。 -/
theorem suffixStart_eq_canonicalStart (D : SpecialC3Data) :
    D.terminalPair.YA = canonicalStart D.terminalPair.R :=
  D.replay.start_eq_canonical_of_quotient_eq_zero D.canonicalBoundary

/-- terminal center差は自動的に非零。 -/
theorem changingCenter (D : SpecialC3Data) :
    center D.terminalPair.A ≠ center D.terminalPair.R :=
  D.terminalPair.center_ne

end SpecialC3Data

namespace SpecialC3At

/-- 無限解析列中の修正後Special C3項から有限snapshotを切り出す。 -/
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
  replay := P.replayCoordinate
  canonicalBoundary := H.canonicalBoundary
  negativePredecessorShadow := H.negativePredecessorShadow

end SpecialC3At

/--
修正後Special C3項が一つの無限解析列から狭義単調な部分列として抽出され、
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

/-- 深さが任意に大きい修正後Special C3部分列が存在すること。 -/
def HasArbitrarilyDeepSpecialC3 : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ E : InfiniteTerminalExtraction S,
  ∃ A : InfiniteTerminalAnalysis E,
    Nonempty (ArbitrarilyDeepSpecialC3Data A)

/--
第三bridge。

各無限terminal抽出からpacket列を構成し、alternative exit候補が無限部分列上で
持続するか、深さ非有界な修正後Special C3部分列へ送る。
強いterminal抽出、carry比較構成、無限鳩の巣、bounded-depth rigidityをここへ
集約する。
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
