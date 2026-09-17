import CollatzLean.Collatz3.Mersenne.SourceDefectBridge
import CollatzLean.Collatz3.Mersenne.BoundedBlockDefectEscape

/-!
# Collatz3 Mersenne: fixed-number-of-zeros escape

`BoundedBlockDefectEscape` は coefficient `u` と endpoint `y` の defect を仮定する。
このファイルでは source 本体 `x` の defect bound を `u` へ移す bridge を合成し、
source / target の zero 個数がともに固定上限なら block depth `k` が一様有界、
という fixed-number-of-zeros 版を得る。

one-zero, two-zero, three-zero ... を個別に分岐せず、任意の固定 bounds `A,B` を同時に扱う。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/--
source defect `A` と target defect `B` を固定すると、一般 `BlockData` の depth は一様有界。

これは fixed-number-of-zeros obstruction の直接形。
-/
def BoundedSourceTargetDefectEscape : Prop :=
  ∀ A B : ℕ,
    ∃ K : ℕ,
      ∀ k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost x A →
        Binary.HasZeroDefectAtMost y B →
        k < K

/--
coefficient / target 版 `BoundedBlockDefectEscape` から source / target 版が従う。
深い数論はここでは使わず、source defect bridge だけを合成する。
-/
theorem boundedSourceTargetDefectEscape_of_blockEscape
    (hEscape : BoundedBlockDefectEscape) :
    BoundedSourceTargetDefectEscape := by
  intro A B
  rcases hEscape A B with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y hBlock hSource hTarget
  exact hK k r u x y hBlock
    (hBlock.coefficient_hasZeroDefectAtMost hSource)
    hTarget

/--
ESS 型 `{2,3}`-unit exponent bound から fixed-number-of-zeros escape を直接得る。
-/
theorem boundedSourceTargetDefectEscape_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound) :
    BoundedSourceTargetDefectEscape := by
  exact boundedSourceTargetDefectEscape_of_blockEscape
    (boundedBlockDefectEscape_of_twoThreeUnitBound hSUnit)

/--
指定した source / target defect bounds `A,B` に対する block depth bound を直接読む。
-/
theorem exists_blockDepth_bound_of_sourceTargetDefect
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (A B : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost x A →
        Binary.HasZeroDefectAtMost y B →
        k < K := by
  exact boundedSourceTargetDefectEscape_of_twoThreeUnitBound hSUnit A B

end Mersenne
end Collatz3
