import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselThreeLift
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftExposedCriticalizationNormalizedTail

/-!
# 第3例探索 次段 6: normalized terminal tail が 3-lift survivor を一意に決める

3 個の Hensel lift を区別する「次の 3 進 digit」を `ZMod 3` で持つ。
criticalization boundary を通過できる digit は、既存の exact bridge により

  - 2^beattyIndex(a) * normalizedTerminalTail(a)   (mod 3)

ただ一つである。

ここでいう `survives` は、探索器の criticalization-boundary filter を通過することを表す。
従って前段の「少なくとも一つ kill できる」より強く、boundary constraint 自体は
3 候補のうち exact に一つだけを残す。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
criticalization boundary digit と一致する lift digit だけが boundary filter を通過する。
-/
def terminalBoundaryLiftSurvives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (digit : ZMod 3) : Prop :=
  digit = MultiCorner.criticalizationBoundaryDigit P hStart

/--
left cut `a` の normalized terminal tail から survivor digit を exact に読む。
-/
theorem terminalBoundaryLiftSurvives_iff_normalizedTerminalTail
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart)
    (digit : ZMod 3) :
    terminalBoundaryLiftSurvives P hStart digit ↔
      digit =
        ((- (2 : ℤ) ^ beattyIndex a *
            P.criticalizationNormalizedTerminalTail
              a (Nat.le_of_lt ha) : ℤ) : ZMod 3) := by
  unfold terminalBoundaryLiftSurvives
  rw [MultiCorner.criticalizationBoundaryDigit_eq_neg_normalizedTerminalTail
      P hStart ha]

/-- normalized terminal tail が指定する digit 自身は必ず boundary filter を通過する。 -/
theorem normalizedTerminalTail_boundaryLift_survives
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {a : ℕ}
    (ha : a < P.criticalizationStart) :
    terminalBoundaryLiftSurvives P hStart
      ((- (2 : ℤ) ^ beattyIndex a *
          P.criticalizationNormalizedTerminalTail
            a (Nat.le_of_lt ha) : ℤ) : ZMod 3) := by
  rw [terminalBoundaryLiftSurvives_iff_normalizedTerminalTail
      P hStart ha]

/--
boundary filter の survivor は一意。従って 3 進 digit の三択はここで分岐しない。
-/
theorem terminalBoundaryLiftSurvivor_unique
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {d₁ d₂ : ZMod 3}
    (h₁ : terminalBoundaryLiftSurvives P hStart d₁)
    (h₂ : terminalBoundaryLiftSurvives P hStart d₂) :
    d₁ = d₂ := by
  unfold terminalBoundaryLiftSurvives at h₁ h₂
  exact h₁.trans h₂.symm

/-- boundary filter を通る `ZMod 3` digit は exact に一つ存在する。 -/
theorem terminalBoundaryLift_existsUnique
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ∃! digit : ZMod 3,
      terminalBoundaryLiftSurvives P hStart digit := by
  refine ⟨MultiCorner.criticalizationBoundaryDigit P hStart, rfl, ?_⟩
  intro digit hDigit
  exact hDigit

end ThirdExampleSearch
end CSTMicro
end Collatz2
