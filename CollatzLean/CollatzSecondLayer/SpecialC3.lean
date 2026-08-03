import CollatzLean.CollatzSecondLayer.ShadowBranches

/-!
# 特殊C3有限障害

first-carryが持ち越され、integer shadowが負であり、
common-centerへ入らない有限packetを特殊C3証人として定義する。
無限軌道そのものは定義に含めないが、元cylinder・terminal pair・carryの
由来等式は有限証人へ保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
polynomial-small canonical C3列から抽出された、
failed-carry・changing-center・negative-shadow型の有限障害。
-/
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

/-- 特殊C3有限障害が存在すること。 -/
def HasSpecialC3 : Prop := Nonempty SpecialC3Data

/--
一つのterminal解析packetは、別出口か特殊C3のどちらかへ必ず落ちる。
この分岐自体には未証明の数学を隠していない。
-/
theorem terminalAnalysis_outcome
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) :
    Nonempty (AlternativeExitData P) ∨
      ∃ _hdefer : DeferredCarry P.carry,
        P.shadow.shadow < 0 ∧
        center P.criticalPair.A ≠ center P.criticalPair.R := by
  rcases carryComparison_split P.carry with hcap | hdefer
  · exact Or.inl ⟨AlternativeExitData.captureSuccess hcap⟩
  · rcases lt_trichotomy P.shadow.shadow 0 with hneg | hzero | hpos
    · by_cases hcenter :
          center P.criticalPair.A = center P.criticalPair.R
      · exact Or.inl ⟨AlternativeExitData.commonCenter hcenter⟩
      · exact Or.inr ⟨hdefer, hneg, hcenter⟩
    · exact Or.inl ⟨AlternativeExitData.zeroShadow hzero⟩
    · exact Or.inl ⟨AlternativeExitData.positiveShadow hpos⟩

/-- terminal解析packetから、別出口または由来情報付き特殊C3を構成する。 -/
theorem alternativeExit_or_specialC3
    {O : OddOrbit}
    {S : C3CylinderSequence O}
    {T : TerminalChainData S}
    (P : TerminalAnalysisPacket S T) :
    HasAlternativeExit ∨ HasSpecialC3 := by
  rcases terminalAnalysis_outcome P with hExit | hSpecial
  · exact Or.inl ⟨O, S, T, P, hExit⟩
  · rcases hSpecial with ⟨hdefer, hneg, hcenter⟩
    exact Or.inr ⟨{
      sourceCylinder := P.sourceCylinder
      terminalPair := P.criticalPair
      sourceRelation := P.sourceRelation
      sourceStart := P.sourceStart
      sourceFinish := P.sourceFinish
      carry := P.carry
      carryOrigin := P.carryOrigin
      deferredCarry := hdefer
      shadow := P.shadow
      negativeShadow := hneg
      changingCenter := hcenter
    }⟩

end CollatzSecondLayer
