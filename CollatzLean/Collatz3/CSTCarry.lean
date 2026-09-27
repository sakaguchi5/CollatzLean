import CollatzLean.Collatz3.CSTCarry.OneModFour
import CollatzLean.Collatz3.CSTCarry.ThreeModFour
import CollatzLean.Collatz3.CSTCarry.TrailingOnes
import CollatzLean.Collatz3.CSTCarry.BinaryWrap
import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import CollatzLean.Collatz3.CSTCarry.BinaryShift
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge
import CollatzLean.Collatz3.CSTCarry.MidpointDuality
import CollatzLean.Collatz3.CSTCarry.FirstPassageBridge
import CollatzLean.Collatz3.CSTCarry.CSTGapBridge
import CollatzLean.Collatz3.CSTCarry.Frontier

set_option linter.style.header false

/-!
# Collatz3.CSTCarry

`4n-3` の即時下降から、first coefficient crossing の Ferrers defect、
fixed-width binary wrap、三進 carry recursion、binary-MSB / ternary-midpoint duality までを
薄い定義と派生定理だけでまとめる追加 package。

既存 `CSTMicro` / `Ferrers.RecordFerrers` の完成済み語彙は再定義しない。
未証明の一般 carry bound は `Frontier` で predicate としてのみ公開する。
-/
