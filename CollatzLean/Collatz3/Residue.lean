import CollatzLean.Collatz3.Arithmetic.ModThreePow
import CollatzLean.Collatz3.Binary.ResidueWeight
import CollatzLean.Collatz3.Binary.ResidueSupport

/-!
# Collatz3 Residue

R1 の semantics 非依存部分をまとめる集約 import。

* mod `3^K` での `2^E` inverse
* `2,6,18,...` residue channel hierarchy
* generic residue support / singleton locking

を含む。actual Collatz run は import しない。
-/
