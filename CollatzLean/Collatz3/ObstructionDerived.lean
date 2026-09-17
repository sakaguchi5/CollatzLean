import CollatzLean.Collatz3.Binary
import CollatzLean.Collatz3.Core.WordFixedPointDerived
import CollatzLean.Collatz3.Mersenne
import CollatzLean.Collatz3.Bridge.Residue
import CollatzLean.Collatz3.Bridge.Mersenne

/-!
# Collatz3: obstruction derived closure

B1/M1/M2/B2/R1/O1 から無条件に導ける追加定理群の集約 import。

* run resolution の有限反復 factor
* singleton residue locking の有限反復
* bounded defect の sparse-complement 表現
* rational fixed point の一意性と符号
* Mersenne affine line の一意性 / composition
* Mersenne macro の residue lift / canonical lift
* one-zero exit の actual exponent word
* one-zero bounded defect の sparse Diophantine equation

をまとめる。C1 の外部 growth hypothesis は import しない。
-/
