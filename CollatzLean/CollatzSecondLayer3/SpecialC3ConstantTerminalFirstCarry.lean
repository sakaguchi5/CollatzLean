import CollatzLean.CollatzSecondLayer3.SpecialC3ConstantTerminalCarryPattern
import CollatzLean.CollatzFirstLayer.NegativeShadowCriticalBoundary

/-!
# Constant terminal nested pairのcritical first-carry境界

短いSpecial C3 seedのpredecessor shadowと、長いseed centerを短いwordだけ輸送した状態は、
自然数magnitudeでexactに

`longMagnitude = shortMagnitude + 2 * odd`

だけ離れる。短いSpecial C3 shadowの最初のnegative stepはexponent 1である。
一方、長い輸送magnitudeの`3m-1`を完全2進分解し、
negative-shadow exact one-bit境界定理へ入れると、その指数は少なくとも2になる。

したがってConstant nested pairの共通word終了点では、
二つのnegative shadowが最初の一段で強制的に分岐する。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData
namespace ConstantTerminalNestedAlignmentData

/-- 長い輸送magnitudeの`3m-1`に対する完全2進分解。 -/
noncomputable def longTransportFactor
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    PositiveExactTwoFactorData (3 * D.longTransportMagnitude n - 1) :=
  positiveExactTwoFactorData
    (3 * D.longTransportMagnitude n - 1)
    (by
      have hPos := D.longTransportMagnitude_pos n
      omega)

/-- 長い輸送状態のnegative-shadow指数。 -/
noncomputable def longTransportExponent
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  (D.longTransportFactor n).exponent

/-- 長い輸送状態の次magnitude。 -/
noncomputable def longTransportNextMagnitude
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  (D.longTransportFactor n).oddPart

/-- 長い輸送状態の次magnitudeは奇数。 -/
theorem longTransportNextMagnitude_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.longTransportNextMagnitude n) :=
  (D.longTransportFactor n).factorization.2

/-- 長い輸送状態のnegative shadow一段方程式。 -/
theorem longTransportStep_equation
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    2 ^ D.longTransportExponent n *
          D.longTransportNextMagnitude n + 1 =
      3 * D.longTransportMagnitude n := by
  have h :=
    (D.longTransportFactor n).factorization.1
  have hmPos := D.longTransportMagnitude_pos n
  unfold longTransportExponent
    longTransportNextMagnitude
  rw [← h]
  omega

/-- 短いSpecial C3 shadowの最初の次magnitude。 -/
noncomputable def shortNextMagnitude
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) : ℕ :=
  (R.special (D.selectedIndex n)).firstShadowMagnitude

/-- 短いSpecial C3 shadowの最初の次magnitudeは奇数。 -/
theorem shortNextMagnitude_odd
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    Odd (D.shortNextMagnitude n) := by
  exact (R.special (D.selectedIndex n)).firstShadowMagnitude_odd

/-- 短いSpecial C3の最初のnegative-shadow指数は定義上exactに1。 -/
theorem shortShadowExponent_eq_one
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    (R.special (D.selectedIndex n)).firstNegativeShadowStep.exponent = 1 := by
  rfl

/-- 短いSpecial C3 shadowはexact exponent 1を使う。 -/
theorem shortShadowStep_equation_one
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    2 * D.shortNextMagnitude n + 1 =
      3 * D.shortMagnitude n := by
  simpa [shortNextMagnitude, shortMagnitude] using
    (R.special (D.selectedIndex n)).firstShadowStep_equation

/--
exact one-bit alignmentと短側exponent 1をnegative first-carry境界へ入れると、
長い輸送状態の次指数は少なくとも2になる。
-/
theorem longTransportExponent_two_le
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    2 ≤ D.longTransportExponent n := by
  exact
    oddShadowStep_exact_one_bit_forces_other_exponent_two_le
      (D.shortNextMagnitude_odd n)
      (D.longTransportNextMagnitude_odd n)
      (D.finishKernel_odd n)
      (D.shortShadowStep_equation_one n)
      (D.longTransportStep_equation n)
      (by
        unfold longTransportMagnitude
        rfl)

/-- 長い輸送状態は短いSpecial C3と同じ指数1を使えない。 -/
theorem longTransportExponent_ne_one
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.longTransportExponent n ≠ 1 := by
  have h := D.longTransportExponent_two_le n
  omega

/-- exact one-bit境界では短側と長側の最初のnegative-shadow指数が必ず分岐する。 -/
theorem firstShadowExponent_diverges
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    D.longTransportExponent n ≠
      (R.special (D.selectedIndex n)).firstNegativeShadowStep.exponent := by
  rw [D.shortShadowExponent_eq_one n]
  exact D.longTransportExponent_ne_one n

/-- 一つのnested pairで得られるcritical boundary情報を束ねる。 -/
structure ConstantTerminalCriticalBoundaryData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) where
  kernel : ℕ
  kernel_eq : kernel = D.finishKernel n
  kernel_odd : Odd kernel
  magnitudeAlignment :
    D.longTransportMagnitude n =
      D.shortMagnitude n + 2 * kernel
  shortExponent : ℕ
  shortExponent_eq_one : shortExponent = 1
  longExponent : ℕ
  longExponent_eq : longExponent = D.longTransportExponent n
  longExponent_two_le : 2 ≤ longExponent

/-- 各Constant nested pairへcritical boundary dataを自動付加する。 -/
noncomputable def criticalBoundaryData
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    (D : ConstantTerminalNestedAlignmentData R)
    (n : ℕ) :
    ConstantTerminalCriticalBoundaryData D n where
  kernel := D.finishKernel n
  kernel_eq := rfl
  kernel_odd := D.finishKernel_odd n
  magnitudeAlignment := by
    rfl
  shortExponent := 1
  shortExponent_eq_one := rfl
  longExponent := D.longTransportExponent n
  longExponent_eq := rfl
  longExponent_two_le := D.longTransportExponent_two_le n

namespace ConstantTerminalFixedCarryPatternData

/--
carry pattern固定後のnested部分列でも、各連続pairにcritical boundaryが残る。
-/
noncomputable def criticalBoundary
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D)
    (n : ℕ) :
    ConstantTerminalCriticalBoundaryData F.nested n :=
  F.nested.criticalBoundaryData n

/-- pattern固定部分列でも長い輸送側の次指数は2以上。 -/
theorem longTransportExponent_two_le
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D)
    (n : ℕ) :
    2 ≤ F.nested.longTransportExponent n :=
  F.nested.longTransportExponent_two_le n

/-- pattern固定後もexact one-bit地点の最初のshadow指数は必ず分岐する。 -/
theorem firstShadowExponent_diverges
    {O : OddOrbit}
    {R : FutureMinimumSpecialC3TowerData O}
    {D : ConstantTerminalNestedAlignmentData R}
    (F : ConstantTerminalFixedCarryPatternData D)
    (n : ℕ) :
    F.nested.longTransportExponent n ≠
      (R.special (F.nested.selectedIndex n)).firstNegativeShadowStep.exponent :=
  F.nested.firstShadowExponent_diverges n

end ConstantTerminalFixedCarryPatternData
end ConstantTerminalNestedAlignmentData
end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
