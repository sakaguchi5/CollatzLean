import CollatzLean.Collatz3.CSTCarry.OneModFour
import CollatzLean.Collatz3.CSTCarry.ThreeModFour
import CollatzLean.Collatz3.CSTCarry.TrailingOnes
import CollatzLean.Collatz3.CSTCarry.BinaryWrap
import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import CollatzLean.Collatz3.CSTCarry.WrapExceptions
import CollatzLean.Collatz3.CSTCarry.CarryBudget
import CollatzLean.Collatz3.CSTCarry.BinaryShift
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge
import CollatzLean.Collatz3.CSTCarry.CriticalRowEnvelope
import CollatzLean.Collatz3.CSTCarry.FinalWrapLowerBound
import CollatzLean.Collatz3.CSTCarry.FinalWrap26
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

途中 carry の wrap は一律禁止せず、

* first wrap は digit `2` のみ、
* wrap overhang は bounded exception に閉じ込められる、
* digit `0` / `1` が来れば modulus 未満へ復帰する、
* final boundedness は global complement budget と exact に同値、

として扱う。

今回さらに final wrap 側を強化した。

* `CriticalRowEnvelope` で actual first-passage row が持つ最小 envelope を分離、
* strict actual ordering から positive weighted defect の exact 2-adic exponent を回収、
* final wrap なら overhang は正の 4 の倍数、
* 従って `S >= 2^H + 4*3^P`、
* 一方 `P <= 26` では critical defect envelope がこの下界に届かない、
* よって `2 <= P <= 26` の `CriticalCarryRows` では final wrap を排除、

までを `CriticalRowEnvelope` / `FinalWrapLowerBound` / `FinalWrap26` に分離した。

既存 `CSTMicro` / `Ferrers.RecordFerrers` の完成済み語彙は再定義しない。
`Critical.Profile` から actual CSTCarry row list への exact constructor bridge は別責務とし、
未証明 bridge を theorem として置かない。
-/
