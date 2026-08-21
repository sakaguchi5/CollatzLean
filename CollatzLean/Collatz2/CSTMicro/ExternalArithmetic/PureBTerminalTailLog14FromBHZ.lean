import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailLog14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianSquareWindow14FromBHZ

/-!
# Pure B terminal log^14 localization, with the square-window parameter discharged

前ファイルで

  BHZCriticalInitialSquareBand + RhinLinearForm14
    -> CriticalSturmianSquareWindow14

を構成したので、既存 `PureBTerminalTailLog14` の theorem から abstract `W` 引数を消す。

ここで残る外部数学は二つだけ:

1. `RhinLinearForm14` -- 既存の linear-form theorem interface。
2. `BHZCriticalInitialSquareBand` -- pure Sturmian initial-power / Ostrowski theorem interface。

Collatz / Pure B 側には追加仮定を置かない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- 実際に使う explicit constant。 -/
def terminalBHZLog14ConstantExplicit
    (B : BHZCriticalInitialSquareBand) : ℕ :=
  2 * criticalSquareWindowGrowthConstant B * 19 ^ 14

namespace PureBProfileObstruction

/--
BHZ/Ostrowski band theorem と Rhin を直接引数にした canonical log^14 localization。
-/
theorem criticalizationTail_le_log14_from_BHZ
    (B : BHZCriticalInitialSquareBand)
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart) :
    P.m - P.criticalizationStart ≤
      terminalBHZLog14ConstantExplicit B *
        (Nat.log 2 (P.m + 1) + 2) ^ 14 := by
  let W := criticalSturmianSquareWindow14FromBHZ B R
  have h := P.criticalizationTail_le_log14 W R hy hStartPos
  have hConst :
      terminalSquareLog14Constant W =
        terminalBHZLog14ConstantExplicit B := by
    simp [
      W,
      terminalSquareLog14Constant,
      terminalBHZLog14ConstantExplicit
    ]
  rw [hConst] at h
  exact h

end PureBProfileObstruction

/-- actual minimal B 用の最終 wrapper。 -/
theorem MinimalActualABObstructionPacket.criticalizationTail_le_log14_from_BHZ
    (B : BHZCriticalInitialSquareBand)
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    P.m - P.criticalizationStart ≤
      terminalBHZLog14ConstantExplicit B *
        (Nat.log 2 (P.m + 1) + 2) ^ 14 := by
  let P := M.toPureBProfileObstruction hL
  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  exact P.criticalizationTail_le_log14_from_BHZ B R hy hStart

end ExternalArithmetic
end CSTMicro
end Collatz2
