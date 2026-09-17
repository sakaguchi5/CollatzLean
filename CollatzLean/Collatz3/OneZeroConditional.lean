import CollatzLean.Collatz3.OneZeroConditional.Basic
import CollatzLean.Collatz3.OneZeroConditional.RegionEscapeDerived

-- C1 の従来 interface
import CollatzLean.Collatz3.OneZeroConditional.StableDefectGrowth
import CollatzLean.Collatz3.OneZeroConditional.Pow3RunGrowth
import CollatzLean.Collatz3.OneZeroConditional.SparseWindowGrowth
import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectEscape

-- reduction と外部 powers-of-three growth の分離
import CollatzLean.Collatz3.OneZeroConditional.ComplexityReduction
import CollatzLean.Collatz3.OneZeroConditional.ComplexityGrowth
import CollatzLean.Collatz3.OneZeroConditional.ComplexityEscape

-- sparse-complement equation を直接使う closure route
import CollatzLean.Collatz3.OneZeroConditional.SparseEquationEscape

-- sparse equation -> nondegenerate {2,3}-S-unit -> ESS 型 bound
import CollatzLean.Collatz3.Mersenne.OneZeroSUnitReduction
import CollatzLean.Collatz3.OneZeroConditional.SUnitEscape

-- global escape の sequence-level consequences
import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectConsequences

/-!
# Collatz3 C1: one-zero conditional bounded-defect escape

O1 の無条件 reduction に、まだ Lean 内で閉じていない digit-complexity / Baker / S-unit 型入力を
薄い `Prop` interface として接続する conditional package。

従来の三領域 interface に加え、

* overlap / periodic の Collatz 側 reduction と powers-of-three growth の分離
* sparse-complement Diophantine equation からの直接 closure
* sparse equation から nondegenerate `{2,3}`-S-unit equation までの無条件 reduction
* ESS 型 bounded-exponent interface から `SparseComplementEquationEscape` への導出
* global escape の sequence-level 帰結

を含む。

`axiom` は導入しない。
-/
