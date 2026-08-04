import CollatzLean.CollatzSecondLayer2.Arithmetic
import CollatzLean.CollatzSecondLayer2.AffineTransport
import CollatzLean.CollatzSecondLayer2.InfiniteOrbit
import CollatzLean.CollatzSecondLayer2.FutureMinimum
import CollatzLean.CollatzSecondLayer2.FirstCrossing
import CollatzLean.CollatzSecondLayer2.TwoAdicShell
import CollatzLean.CollatzSecondLayer2.CaptureWindow
import CollatzLean.CollatzSecondLayer2.SpecialC3
import CollatzLean.CollatzSecondLayer2.WindowAnalysis
import CollatzLean.CollatzSecondLayer2.Synchronization
import CollatzLean.CollatzSecondLayer2.AlternativeExclusion
import CollatzLean.CollatzSecondLayer2.CaptureRefinement
import CollatzLean.CollatzSecondLayer2.TransportRefinement
import CollatzLean.CollatzSecondLayer2.MovingAnchorObstruction
import CollatzLean.CollatzSecondLayer2.Reduction

/-!
# CollatzSecondLayer2

旧`CollatzSecondLayer`をimportせず、第一層のみから再構成した第二層。

公開する中心API:

* `OddOrbit`
* `OddOrbit.futureMinimumSequence`
* `MovingFirstCrossingData`
* `OddOrbit.CapturedWindowAt`
* `OddOrbit.SynchronizedWindowAt`
* `SpecialC3At`
* `MovingAnchorExpandingBlockObstructionData`
* `unboundedOrbit_trichotomy_on`
* `unbounded_odd_orbit_trichotomy`
-/
