import CollatzLean.CollatzSecondLayer.TerminalChain
import CollatzLean.CollatzFirstLayer.DepthCoefficient

/-!
# first-carry・center・integer shadowの有限分岐

ここでは、特殊C3へ残る前に別出口へ進む三種類目の例外を、
first-carry成功、正または零shadow、common-center合流として明示する。
terminal chain、解析packet、carryの由来をすべて型のフィールドとして保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 自然数に限定しない有限語のアフィン実現式。 -/
def RealizesInt (w : ExpWord) (x y : ℤ) : Prop :=
  (2 : ℤ) ^ twoSteps w * y =
    (3 : ℤ) ^ oddSteps w * x + affineConstInt w

/-- canonical開始値に対応する通常の整数shadow。 -/
structure CanonicalShadowData (w : ExpWord) where
  shadow : ℤ
  realizes : RealizesInt w (canonicalStart w : ℤ) shadow

/-- first-carry二分岐を適用できる有限整数データ。 -/
structure CarryComparison where
  x : ℕ
  y : ℕ
  d : ℕ
  e : ℕ
  a : ℕ
  u : ℕ
  depth_le : d ≤ e
  difference : y = x + 2 ^ d * u
  difference_odd : Odd u
  lower_factorization : 3 * x + 1 = 2 ^ e * a
  lower_odd : Odd a

/--
carry比較がterminal pairの二つの実終点から作られたことを表す。

`difference` と `difference_odd` により `d` は `YAR - YA` の正確な2進深さ、
`lower_factorization` と `lower_odd` により `e` は `3 * YA + 1` の
正確な2進深さとして既に証明されている。
-/
structure CarryOrigin
    (T : TerminalPairData) (C : CarryComparison) : Prop where
  lowerValue : C.x = T.YA
  upperValue : C.y = T.YAR

/-- first-carryが差の深さで捕捉される枝。 -/
structure CapturedCarry (C : CarryComparison) : Type where
  depth_lt : C.d < C.e
  oddPart : ℕ
  exactFactor :
    ExactTwoFactor (3 * C.y + 1) C.d oddPart

/-- 深さが等しく、carryが少なくとも1ビット持ち越される枝。 -/
structure DeferredCarry (C : CarryComparison) : Type where
  depth_eq : C.d = C.e
  quotient : ℕ
  extraFactor :
    3 * C.y + 1 = 2 ^ (C.d + 1) * quotient

/--
first-carryの命題的二分岐から、
データを保持する二分岐が少なくとも一つ存在する。
-/
theorem carryComparison_split_nonempty
    (C : CarryComparison) :
    Nonempty (CapturedCarry C ⊕ DeferredCarry C) := by
  rcases first_carry_split
      C.depth_le
      C.difference
      C.difference_odd
      C.lower_factorization
      C.lower_odd with h | h
  · rcases h with ⟨hlt, b, hb⟩
    exact ⟨Sum.inl ⟨hlt, b, hb⟩⟩
  · rcases h with ⟨heq, q, hq⟩
    exact ⟨Sum.inr ⟨heq, q, hq⟩⟩

/--
first-carry分岐の有限データを古典選択で一つ取り出す。
-/
noncomputable def carryComparison_split
    (C : CarryComparison) :
    CapturedCarry C ⊕ DeferredCarry C :=
  Classical.choice (carryComparison_split_nonempty C)

/--
terminal chainから切り出す、由来情報付き有限分岐判定packet。

`entry_mem` により任意のterminal pairを後付けできず、
`carryOrigin` によりcarry比較の二値もそのentryの実終点へ固定される。
-/
structure TerminalAnalysisPacket
    {O : OddOrbit}
    (S : C3CylinderSequence O)
    (T : TerminalChainData S) where
  entry : TerminalChainEntry S
  entry_mem : entry ∈ T.entry
  carry : CarryComparison
  carryOrigin : CarryOrigin entry.pair carry
  shadow : CanonicalShadowData entry.pair.R

namespace TerminalAnalysisPacket

/-- packetが参照する元cylinderの有限snapshot。 -/
def sourceCylinder
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) : CanonicalC3Witness :=
  (S.cylinder P.entry.sourceIndex).snapshot

/-- packetが参照するterminal pair。 -/
def criticalPair
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) : TerminalPairData :=
  P.entry.pair

/-- terminal pair全体の語は元cylinder語そのものである。 -/
theorem sourceRelation
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) :
    P.criticalPair.A ++ P.criticalPair.R =
      P.sourceCylinder.word :=
  P.entry.sourceRelation

/-- terminal pairの開始値は元cylinderの開始値である。 -/
theorem sourceStart
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) :
    P.criticalPair.X = P.sourceCylinder.start :=
  P.entry.sourceStart

/-- terminal pair全体の終点は元cylinderの終点である。 -/
theorem sourceFinish
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) :
    P.criticalPair.YAR = P.sourceCylinder.finish :=
  P.entry.sourceFinish

end TerminalAnalysisPacket

/-- 特殊C3になる前に別出口へ進む有限証人。 -/
inductive AlternativeExitData
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) : Type
  | captureSuccess (h : CapturedCarry P.carry)
  | positiveShadow (h : 0 < P.shadow.shadow)
  | zeroShadow (h : P.shadow.shadow = 0)
  | commonCenter
      (h : center P.criticalPair.A = center P.criticalPair.R)

/-- 第三の例外：特殊C3になる前の別出口が存在する。 -/
def HasAlternativeExit : Prop :=
  ∃ O : OddOrbit,
  ∃ S : C3CylinderSequence O,
  ∃ T : TerminalChainData S,
  ∃ P : TerminalAnalysisPacket S T,
    Nonempty (AlternativeExitData P)

/-- terminal chainごとに、そこから抽出された解析packetを供給するbridge。 -/
def TerminalAnalysisPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ T : TerminalChainData S,
    Nonempty (TerminalAnalysisPacket S T)

end CollatzSecondLayer
