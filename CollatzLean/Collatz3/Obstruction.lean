import CollatzLean.Collatz3.Core.WordFixedPoint
import CollatzLean.Collatz3.Bridge.CycleResidue
import CollatzLean.Collatz3.Mersenne.MacroLine
import CollatzLean.Collatz3.Mersenne.OneZeroRegions

/-!
# Collatz3 O1: obstruction reductions

O1 の無条件 reduction 層の集約 import。

* exponent word の rational fixed point
* cycle residue の一歩必要条件
* fixed `(d,r)` Mersenne macro affine line
* one-zero exit と stable / overlap / periodic 三分割

までをまとめる。
外部の Baker / Stephan 型 growth theorem はここへ入れない。
-/
