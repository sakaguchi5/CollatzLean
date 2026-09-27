import CollatzLean.Collatz3.CSTCarry.OneModFour
import CollatzLean.Collatz3.CSTCarry.ThreeModFour
import CollatzLean.Collatz3.CSTCarry.TrailingOnes
import CollatzLean.Collatz3.CSTCarry.BinaryWrap
import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import CollatzLean.Collatz3.CSTCarry.WrapExceptions
import CollatzLean.Collatz3.CSTCarry.CarryBudget
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
fixed-width binary wrap、三進 carry recursion、binary-MSB / ternary-midpoint dualityまでを
薄い定義と派生定理だけでまとめる追加 package。

今回さらに、途中 carry の wrap を一律禁止するのではなく、

* first wrap は digit `2` のみ、
* wrap overhang は `M/4` 未満に閉じ込められる、
* digit `0` / `1` が来れば modulus 未満へ復帰する、
* final wrap なら末尾 digit は `2`、complement 側では末尾 `0`、
* final boundedness は global complement budget と exact に同値、

という「例外付き wrap 分類」を `WrapExceptions` / `CarryBudget` に分離した。

既存 `CSTMicro` / `Ferrers.RecordFerrers` の完成済み語彙は再定義しない。
RecordFerrers から actual CSTCarry row list への未完成 bridge は theorem として捏造せず、
未証明の一般 final carry bound は引き続き `Frontier` の研究目標として扱う。
-/
