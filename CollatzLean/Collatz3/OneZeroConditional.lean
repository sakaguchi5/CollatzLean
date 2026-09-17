import CollatzLean.Collatz3.OneZeroConditional.Basic
import CollatzLean.Collatz3.OneZeroConditional.StableDefectGrowth
import CollatzLean.Collatz3.OneZeroConditional.Pow3RunGrowth
import CollatzLean.Collatz3.OneZeroConditional.SparseWindowGrowth
import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectEscape

/-!
# Collatz3 C1: one-zero conditional bounded-defect escape

O1 の三領域 reduction に、まだ Lean 内で閉じていない digit-complexity / Baker 型入力を
薄い `Prop` interface として接続する conditional package。

`axiom` は導入しない。
-/
