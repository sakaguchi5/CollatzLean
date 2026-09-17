import CollatzLean.Collatz3.OneZeroConditional.Basic

/-!
# Collatz3 OneZeroConditional: power-of-three run-growth interface

overlap region では bounded endpoint defect が `3^k` の binary run complexity を
一様有界に押し込む、という O1 reduction と、power-of-three run growth を合わせた後に
必要となる最小 interface を保存する。

Stephan 型の定量定理そのものはここでは primitive / axiom にしない。
-/

namespace Collatz3
namespace OneZeroConditional

/-- overlap region に対する eventual escape interface。 -/
def Pow3RunGrowth : Prop :=
  EventualRegionEscape Mersenne.InOverlapRegion

end OneZeroConditional
end Collatz3
