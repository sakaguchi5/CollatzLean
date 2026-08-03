import CollatzLean.CollatzSecondLayer.ShadowBranches

/-!
# 特殊C3有限障害

first-carryが持ち越され、integer shadowが負であり、
common-centerへ入らない有限packetを特殊C3証人として定義する。
無限軌道そのものは定義に含めない。
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
  sourceRelation : terminalPair.R = sourceCylinder.word
  carry : CarryComparison
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
    (P : TerminalAnalysisPacket) :
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

/-- terminal解析packetから、別出口または特殊C3を構成する。 -/
theorem alternativeExit_or_specialC3
    (P : TerminalAnalysisPacket) :
    HasAlternativeExit ∨ HasSpecialC3 := by
  rcases terminalAnalysis_outcome P with hExit | hSpecial
  · exact Or.inl ⟨P, hExit⟩
  · rcases hSpecial with ⟨hdefer, hneg, hcenter⟩
    exact Or.inr ⟨{
      sourceCylinder := P.sourceCylinder
      terminalPair := P.criticalPair
      sourceRelation := P.sourceRelation
      carry := P.carry
      deferredCarry := hdefer
      shadow := P.shadow
      negativeShadow := hneg
      changingCenter := hcenter
    }⟩

end CollatzSecondLayer
