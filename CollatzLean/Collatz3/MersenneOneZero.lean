import CollatzLean.Collatz3.Binary
import CollatzLean.Collatz3.Bridge.Mersenne

/-!
# Collatz3: one-zero Mersenne first package

第一実装フェーズ B1 -> M1 -> M2 の集約 import。

* binary alternating weight / zero defect
* Mersenne block の exact 整数算術
* one-zero source と exit depth
* block exponent word
* actual odd-only `Runs` への bridge

を一つの入口から利用できるようにする。
新しい数学的定義は置かない。
-/
