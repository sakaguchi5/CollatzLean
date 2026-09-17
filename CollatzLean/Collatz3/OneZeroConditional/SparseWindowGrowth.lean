import CollatzLean.Collatz3.OneZeroConditional.Basic

/-!
# Collatz3 OneZeroConditional: sparse-window growth interface

periodic region では bounded endpoint defect が `3^k` の可変-period binary window を
bounded-complexity にする。Baker / sparse-window gap principle でこれを排除するために
後段が必要とする最小 interface だけを保存する。
-/

namespace Collatz3
namespace OneZeroConditional

/-- periodic region に対する eventual escape interface。 -/
def SparseWindowGrowth : Prop :=
  EventualRegionEscape Mersenne.InPeriodicRegion

end OneZeroConditional
end Collatz3
