import CollatzLean.Collatz3.OneZeroConditional.Basic

/-!
# Collatz3 OneZeroConditional: stable-region defect growth interface

stable region の exact binary-complement analysis が与えるべき最小 interface。

このファイルでは analytic / digit-complexity theorem を仮定として追加せず、
必要な eventual escape property に名前を与えるだけに留める。
-/

namespace Collatz3
namespace OneZeroConditional

/-- stable region では bounded endpoint defect を保ったまま `k→∞` にできない。 -/
def StableDefectGrowth : Prop :=
  EventualRegionEscape Mersenne.InStableRegion

end OneZeroConditional
end Collatz3
