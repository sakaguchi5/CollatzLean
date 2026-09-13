import CollatzLean.Collatz3.Bridge.CriticalMargin
import CollatzLean.Collatz3.Bridge.CoefficientFirstPassage
import CollatzLean.Collatz3.Bridge.CriticalCorrectionLowerBound
import CollatzLean.Collatz3.Bridge.CriticalCorrectionUpperBound
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.MultiCollisionPenalty
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.CollisionFreeRigidity

/-!
# Collatz3: critical-margin / multi-collision package 1--6

`db6eee3b300328f1089311a1fca5d6c7d9a593e3` を基準に、次の六段をまとめて import する。

1. critical margin と rank-drop determinant
2. coefficient first-passage -> existing CriticalFirstPassage
3. actual correction sum の necessary lower bound
4. high-orbit correction budget upper bound
5. multiple collision の additive / gcd-quadratic area penalty
6. collision-free branch の internal tight recurrence

このファイル自身には新しい定義・定理を置かない。
-/
