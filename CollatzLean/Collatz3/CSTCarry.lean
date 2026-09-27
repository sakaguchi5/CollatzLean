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
import CollatzLean.Collatz3.CSTCarry.ProfileRowBridge
import CollatzLean.Collatz3.CSTCarry.FirstPassageRowBridge
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

final wrap 側ではさらに、

* critical row envelope から `S <= criticalWeightedDefectUpper P`、
* strict actual ordering から positive weighted defect の exact 2-adic exponent、
* final wrap なら overhang は正の 4 の倍数、
* 従って `S >= 2^H + 4*3^P`、
* `2 <= P <= 26` では両 bound が矛盾するため final wrap を排除、

まで証明済み。

今回 `ProfileRowBridge` / `FirstPassageRowBridge` を追加し、以前は外部仮定だった

  Critical.Profile / FirstPassagePath -> CriticalCarryRows

を閉じる。

* admissible profile の row を
  `boundary = beattyIndex r`, `actual = checkpoint h r` と canonical に構成、
* row を `r=m-1,...,0` の terminal-to-initial 順に並べると
  `CriticalCarryRows m` を満たす、
* standard parity `FirstPassagePath` を odd-only exponent word へ exact に圧縮し、
  `IsCriticalWord -> profileOfWord -> CriticalCarryRows` まで接続、
* その結果 `2 <= p <= 26` では FirstPassagePath 由来 rows に対して
  `CriticalCarryRows` を別仮定せず final-wrap 排除定理を適用できる。

なお、actual arithmetic からこの canonical rows 上の `CarryRealizes` witness を構成する
三進 recurrence の存在・同定は別責務であり、この bridge では捏造しない。
-/
