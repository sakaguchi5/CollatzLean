import CollatzLean.CollatzSecondLayer3.TerminalEscapeExponent
import CollatzLean.CollatzSecondLayer3.SourcePreservingSpecialC3Reduction

/-!
# Constant terminal排除を発散反例全体の否定へ直結する最終還元

新しい主経路はSpecial C3 towerのterminal geometry三分岐を経由しない。
非有界odd-only軌道から標準future-minimumを選び、全長さfirst-deferred系を作る。
Constant terminal Special C3 familyが存在しないならterminal timeは無限遠へ逃げ、
指数tailが最終定数となって非有界性に矛盾する。

従って、発散側の残存数学問題はConstant terminal familyの排除一つに集約される。
-/

namespace CollatzSecondLayer3

open CollatzCore

/--
全ての非有界軌道由来all-length系でConstant terminal familyが存在しない、
というConstant terminal排除原理。
-/
def ConstantTerminalExclusionPrinciple : Prop :=
  ∀ (O : OddOrbit) (A : FutureMinimumAllLengthTerminalData O),
    ¬ Nonempty (FutureMinimumAllLengthTerminalData.ConstantTerminalSpecialC3FamilyData A)

/-- 一つの非有界軌道は、その標準all-length系でConstantを排除すれば矛盾。 -/
theorem unboundedOrbit_impossible_of_no_constantTerminal
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hNoConstant :
      ¬ Nonempty
        (FutureMinimumAllLengthTerminalData.ConstantTerminalSpecialC3FamilyData
          (FutureMinimumAllLengthTerminalData.ofUnbounded O hU))) :
    False := by
  let A := FutureMinimumAllLengthTerminalData.ofUnbounded O hU
  exact A.impossible_of_no_constantTerminal hNoConstant

/--
Constant terminal排除原理から非有界odd-only軌道の不存在が従う。
Increasing eventual-before / cofinal-overlapの個別排除は不要。
-/
theorem no_unbounded_odd_orbit_of_constantTerminal_exclusion
    (hConstant : ConstantTerminalExclusionPrinciple) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases hU with ⟨O, hO⟩
  let A := FutureMinimumAllLengthTerminalData.ofUnbounded O hO
  have hNo :
      ¬ Nonempty
        (FutureMinimumAllLengthTerminalData.ConstantTerminalSpecialC3FamilyData A) :=
    hConstant O A
  exact A.impossible_of_no_constantTerminal hNo

end CollatzSecondLayer3
