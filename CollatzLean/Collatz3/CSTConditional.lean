import CollatzLean.Collatz3.CSTConditional.GlobalCST
import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.CSTConditional.MarginMass
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.CSTConditional.ACCounting
import CollatzLean.Collatz3.CSTConditional.ACConservation
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth
import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape

/-!
# Collatz3: CSTConditional package

`GlobalCST` を仮定した場合だけ使う条件付き bridge 群。
既存 unconditional kernel / Bridge / CSTMicro の定理そのものは変更しない。

追加の AC / A-type package では、Global CST により `B` が消えた後の future-minimum dynamics を

* exact two-depth / margin threshold
* `C / AC / AAC` 局所 cell
* `#A + #C = q`
* `defectGrowth + #C = q`
* defect / critical-margin exact conservation
* linear defect lower bound から future-minimum 密度・平均 block 長・actual log growth
* linear defect survivor の normalized escape coordinate の有限正実数極限

として整理する。
-/
