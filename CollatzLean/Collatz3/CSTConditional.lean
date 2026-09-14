import CollatzLean.Collatz3.CSTConditional.GlobalCST
import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.CSTConditional.MarginMass
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.CSTConditional.ACCounting
import CollatzLean.Collatz3.CSTConditional.ACConservation

/-!
# Collatz3: CSTConditional package

`GlobalCST` を仮定した場合だけ使う条件付き bridge 群。
既存 unconditional kernel / Bridge / CSTMicro の定理そのものは変更しない。

追加の AC package では、Global CST により `B` が消えた後の future-minimum dynamics を

* exact two-depth / margin threshold
* `C / AC / AAC` 局所 cell
* `#A + #C = q`
* `defectGrowth + #C = q`
* defect / critical-margin exact conservation

として整理する。
-/
