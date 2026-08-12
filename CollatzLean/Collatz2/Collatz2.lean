import CollatzLean.Collatz2.Core.Word
import CollatzLean.Collatz2.Core.AffineTransfer
import CollatzLean.Collatz2.Core.Realization
import CollatzLean.Collatz2.Core.Interval
import CollatzLean.Collatz2.Local.DeterminantSign
import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Local.Defect
import CollatzLean.Collatz2.Local.FirstCrossing
import CollatzLean.Collatz2.Local.SuffixDeterminantProfile
import CollatzLean.Collatz2.Canonical.ResidueClass
import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Canonical.ReplayExtremality

/-!
# Collatz2

旧 `CollatzLean.Collatz.*` を import しない独立再構築の入口。

第1段階では lossless な有限語・affine transfer・realization・interval decomposition を
正本として構築し、Expanding / Contracting を determinant sign のコロラリーとして導いた。

第2段階では stepwise Runs と signed defect を導入し、PositiveReturn を defect sign、
FirstCrossing を determinant sign change、AllSuffixesContracting を suffix determinant profile
のコロラリーとして再構成した。

第3段階では odd-endpoint realization の合同類を先に構築し、その最小非負代表として
canonical start を導く。normalized Runs の endpoint odd から ReplayCoordinate を構成し、
contracting replay では determinant の負符号から `q = 0` が最大 displacement layer であること、
従って旧 `j = 0` 型の canonical positive return が corollary として現れることを示す。
-/
