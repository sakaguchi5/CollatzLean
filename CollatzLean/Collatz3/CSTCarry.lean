import CollatzLean.Collatz3.CSTCarry.OneModFour
import CollatzLean.Collatz3.CSTCarry.ThreeModFour
import CollatzLean.Collatz3.CSTCarry.TrailingOnes
import CollatzLean.Collatz3.CSTCarry.BinaryWrap
import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import CollatzLean.Collatz3.CSTCarry.CarryDeterministic
import CollatzLean.Collatz3.CSTCarry.WrapExceptions
import CollatzLean.Collatz3.CSTCarry.CarryBudget
import CollatzLean.Collatz3.CSTCarry.TernaryCorrection
import CollatzLean.Collatz3.CSTCarry.BinaryShift
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge
import CollatzLean.Collatz3.CSTCarry.CriticalRowEnvelope
import CollatzLean.Collatz3.CSTCarry.FinalWrapLowerBound
import CollatzLean.Collatz3.CSTCarry.FinalWrap26
import CollatzLean.Collatz3.CSTCarry.ProfileRowBridge
import CollatzLean.Collatz3.CSTCarry.FirstPassageRowBridge
import CollatzLean.Collatz3.CSTCarry.FirstPassageCanonicalCarry
import CollatzLean.Collatz3.CSTCarry.MidpointDuality
import CollatzLean.Collatz3.CSTCarry.FirstPassageBridge
import CollatzLean.Collatz3.CSTCarry.CSTGapBridge
import CollatzLean.Collatz3.CSTCarry.Frontier
/-
# Collatz3 CSTCarry: Ferrers affine/residue program aggregate


1. `S = B_boundary - B_actual` の exact affine difference。
2. affine difference と binary start residue displacement の exact bridge。
3. 1-cell / finite Ferrers chain の residue displacement law。
4. final carry の `residue + 2^H * quotient` exact lift。
5. critical rows では quotient が `0/1` に限られ、任意幅 final-wrap 問題が
   `CriticalLiftZero` / complement budget positivity に exact に縮約されること。

未証明なのは最後の `CriticalLiftZero` 自体であり、ここでは仮定や theorem として捏造しない。
-/
import CollatzLean.Collatz3.CSTCarry.FerrersAffineBudget
import CollatzLean.Collatz3.CSTCarry.ProfileAffineBudgetBridge
import CollatzLean.Collatz3.CSTCarry.FerrersAffineResidueBridge
import CollatzLean.Collatz3.CSTCarry.CarryLiftQuotient
import CollatzLean.Collatz3.CSTCarry.FerrersResidueFrontier

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

`ProfileRowBridge` / `FirstPassageRowBridge` により、以前は外部仮定だった

  Critical.Profile / FirstPassagePath -> CriticalCarryRows

も閉じている。

今回さらに `CarryDeterministic` / `TernaryCorrection` /
`FirstPassageCanonicalCarry` を追加し、三進 carry recurrence 自身を canonical 化する。

* `2^H` は mod 3 の unit なので各 row digit は一意、
* canonical digit / next carry を逐次定義できる、
* 任意の Ferrers row list に対し `CarryRealizes (2^H)` witness が存在一意、
* digit value は global に
  `- (2^H)^(-1) * ferrersWeightedDefect rows (mod 3^P)`
  の canonical representative と exact に一致、
* FirstPassagePath には canonical ternary digits / final carry が仮定なしで定義できる、
* `2 <= p <= 26` では外部 `CarryRealizes` witness を仮定せず
  canonical final carry が `2^criticalTwoDepth p` 未満、
* 同範囲では canonical final carry と `ferrersBinaryShift` が自然数として exact に一致、

まで接続する。
-/
