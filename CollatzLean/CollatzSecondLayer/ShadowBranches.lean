import CollatzLean.CollatzSecondLayer.TerminalChain
import CollatzLean.CollatzFirstLayer.DepthCoefficient

/-!
# first-carry・center・integer shadowの有限分岐

ここでは、特殊C3へ残る前に別出口へ進む三種類目の例外を、
first-carry成功、正または零shadow、common-center合流として明示する。
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

/-- terminal chainから切り出す、有限分岐判定用packet。 -/
structure TerminalAnalysisPacket where
  sourceCylinder : CanonicalC3Witness
  criticalPair : TerminalPairData
  sourceRelation : criticalPair.R = sourceCylinder.word
  carry : CarryComparison
  shadow : CanonicalShadowData criticalPair.R

/-- 特殊C3になる前に別出口へ進む有限証人。 -/
inductive AlternativeExitData (P : TerminalAnalysisPacket) : Type
  | captureSuccess (h : CapturedCarry P.carry)
  | positiveShadow (h : 0 < P.shadow.shadow)
  | zeroShadow (h : P.shadow.shadow = 0)
  | commonCenter (h : center P.criticalPair.A = center P.criticalPair.R)

/-- 第三の例外：特殊C3になる前の別出口が存在する。 -/
def HasAlternativeExit : Prop :=
  ∃ P : TerminalAnalysisPacket,
    Nonempty (AlternativeExitData P)

/-- terminal chainごとに解析packetを供給するbridge。 -/
def TerminalAnalysisPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : C3CylinderSequence O,
  ∀ _T : TerminalChainData S,
    Nonempty TerminalAnalysisPacket

end CollatzSecondLayer
