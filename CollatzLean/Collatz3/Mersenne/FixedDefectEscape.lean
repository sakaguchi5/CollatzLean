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

/--
source defect が `m` 以下のまま十分深い block に入るなら、
target defect も `m` 以下であることはできない。

つまり、固定 defect `m` を保ったまま arbitrarily deep block を通ることはできない、
という `BoundedSourceTargetDefectEscape` の直接の対偶形。
-/
theorem deepBlock_forces_targetDefect_above_bound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (m : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost x m →
        K ≤ k →
        ¬ Binary.HasZeroDefectAtMost y m := by
  rcases exists_blockDepth_bound_of_sourceTargetDefect hSUnit m m with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y hBlock hSource hk hTarget
  have hkLt : k < K :=
    hK k r u x y hBlock hSource hTarget
  omega

/--
source が exact に `m` 個の zero を持ち、
target が exact に `targetDefect` 個の zero を持つとする。

block depth が十分大きければ

`m < targetDefect`

が必ず成り立つ。

したがって十分深い block は binary zero defect を厳密に増加させる。
-/
theorem deepBlock_forces_strict_zeroDefect_growth
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (m : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y sourceLength targetDefect targetLength : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefect x m sourceLength →
        Binary.HasZeroDefect y targetDefect targetLength →
        K ≤ k →
        m < targetDefect := by
  rcases deepBlock_forces_targetDefect_above_bound hSUnit m with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y sourceLength targetDefect targetLength
    hBlock hSourceExact hTargetExact hk
  have hSourceAtMost : Binary.HasZeroDefectAtMost x m :=
    Binary.HasZeroDefectAtMost.of_exact hSourceExact (by omega)
  have hNotTargetAtMost :
      ¬ Binary.HasZeroDefectAtMost y m :=
    hK k r u x y hBlock hSourceAtMost hk
  by_contra hNotGreater
  have hTargetLe : targetDefect ≤ m := by
    omega
  have hTargetAtMost : Binary.HasZeroDefectAtMost y m :=
    Binary.HasZeroDefectAtMost.of_exact hTargetExact hTargetLe
  exact hNotTargetAtMost hTargetAtMost

end Mersenne
end Collatz3
