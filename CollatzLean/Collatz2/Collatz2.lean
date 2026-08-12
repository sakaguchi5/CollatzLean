import CollatzLean.Collatz2.Core.Word
import CollatzLean.Collatz2.Core.AffineTransfer
import CollatzLean.Collatz2.Core.Realization
import CollatzLean.Collatz2.Core.Interval
import CollatzLean.Collatz2.Local.DeterminantSign

/-!
# Collatz2

旧 `CollatzLean.Collatz.*` を import しない独立再構築の入口。

第1段階では lossless な有限語・affine transfer・realization・interval decomposition を
正本として構築し、Expanding / Contracting を determinant sign のコロラリーとして導く。
-/
