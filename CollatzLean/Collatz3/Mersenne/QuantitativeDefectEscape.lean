import CollatzLean.Collatz3.Mersenne.TwoSidedSparseDefectEscape
import CollatzLean.Collatz3.Mersenne.SourceDefectBridge

/-!
# Collatz3 Mersenne: hole complexity から binary defect 下界へ

以前の定量層は

`k < F(A+B+5)`

という exponent-bound function を経由していた。
この向きでは `F` の逆関数を改めて解析する必要がある。

ここでは exact block-sparse equation の hole lower bound

`G(k) ≤ source holes + target holes`

を直接 binary defect へ戻す。

その結果、将来 `G(k) ≍ log k / log log k` のような定理が得られれば、
逆関数を挟まずそのまま defect 下界になる。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/--
coefficient `u` の defect が `A` 以下、target `y` の defect が `B` 以下なら、
合計 `A+B` holes 以下の sparse endpoint complements を持つ。
-/
theorem sparseEndpointComplementsAtMost_of_coefficientTargetDefect
    {u y A B : ℕ}
    (hSource : Binary.HasZeroDefectAtMost u A)
    (hTarget : Binary.HasZeroDefectAtMost y B) :
    SparseEndpointComplementsAtMost u y (A + B) := by
  rcases hSource.exists_sparseComplement with
    ⟨sourceLength, sourceBits, hSourceLen, hSourceCount, hSourceEq⟩
  rcases hTarget.exists_sparseComplement with
    ⟨targetLength, targetBits, hTargetLen, hTargetCount, hTargetEq⟩
  refine ⟨sourceLength, targetLength, sourceBits, targetBits,
    hSourceLen, hTargetLen, ?_, hSourceEq, hTargetEq⟩
  omega

/--
source 本体 `x` の defect bound を coefficient `u` へ移して、
同じ `A+B` hole bound を得る。
-/
theorem sparseEndpointComplementsAtMost_of_sourceTargetDefect
    {k r u x y A B : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefectAtMost x A)
    (hTarget : Binary.HasZeroDefectAtMost y B) :
    SparseEndpointComplementsAtMost u y (A + B) := by
  exact sparseEndpointComplementsAtMost_of_coefficientTargetDefect
    (hBlock.coefficient_hasZeroDefectAtMost hSource)
    hTarget

/--
source defect が exact に正の `m`、target defect が exact に `b` なら、
coefficient 側では境界 zero が一つ消えるため、hole complexity は

`(m-1) + b`

まで詰められる。
-/
theorem sparseEndpointComplementsAtMost_of_exact_sourceTarget
    {k r u x y sourceDefect sourceLength targetDefect targetLength : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefect x sourceDefect sourceLength)
    (hTarget : Binary.HasZeroDefect y targetDefect targetLength)
    (hSourcePos : 0 < sourceDefect) :
    SparseEndpointComplementsAtMost
      u y ((sourceDefect - 1) + targetDefect) := by
  rcases hBlock.exists_coefficient_zeroDefect_eq_pred hSource hSourcePos with
    ⟨coefficientLength, hCoefficient⟩
  rcases hCoefficient.exists_sparseComplement with
    ⟨sourceBits, hSourceLen, hSourceCount, hSourceEq⟩
  rcases hTarget.exists_sparseComplement with
    ⟨targetBits, hTargetLen, hTargetCount, hTargetEq⟩
  refine ⟨coefficientLength, targetLength, sourceBits, targetBits,
    hSourceLen, hTargetLen, ?_, hSourceEq, hTargetEq⟩
  calc
    Binary.oneCount sourceBits + Binary.oneCount targetBits
        = (sourceDefect - 1) + targetDefect := by
            rw [hSourceCount, hTargetCount]
    _ ≤ (sourceDefect - 1) + targetDefect := le_rfl

/--
exact block-sparse complexity lower bound `G` から、bounded source/target defect の和に
直接下界を得る。

`F` やその逆関数は使わない。
-/
theorem sourceTargetDefect_ge_blockSparseLowerBound
    {G : ℕ → ℕ}
    (hLower : BlockSparsePow3LowerBound G)
    {A B k r u x y : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefectAtMost x A)
    (hTarget : Binary.HasZeroDefectAtMost y B) :
    G k ≤ A + B := by
  apply blockSparseLowerBound_of_sparseComplements hLower hBlock
  exact sparseEndpointComplementsAtMost_of_sourceTargetDefect
    hBlock hSource hTarget

/--
exact source defect が正なら、source→coefficient で zero が一つ消える分だけ強く、

`G(k) + 1 ≤ sourceDefect + targetDefect`

を得る。
-/
theorem exactTotalDefect_succ_ge_blockSparseLowerBound
    {G : ℕ → ℕ}
    (hLower : BlockSparsePow3LowerBound G)
    {k r u x y sourceDefect sourceLength targetDefect targetLength : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefect x sourceDefect sourceLength)
    (hTarget : Binary.HasZeroDefect y targetDefect targetLength)
    (hSourcePos : 0 < sourceDefect) :
    G k + 1 ≤ sourceDefect + targetDefect := by
  have hSparse :=
    sparseEndpointComplementsAtMost_of_exact_sourceTarget
      hBlock hSource hTarget hSourcePos
  have hLower' :
      G k ≤ (sourceDefect - 1) + targetDefect :=
    blockSparseLowerBound_of_sparseComplements hLower hBlock hSparse
  omega

/--
既存 ESS 型仮定だけでも、source defect と target defect の和を固定したまま
block depth を arbitrarily large にすることはできない。

従来の `A`,`B` を別々に固定する形より、quantitative target に近い「total defect」版。
-/
theorem exists_depth_bound_of_totalDefect
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (D : ℕ) :
    ∃ K : ℕ,
      ∀ A B k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost x A →
        Binary.HasZeroDefectAtMost y B →
        A + B ≤ D →
        k < K := by
  rcases blockSparsePow3Escape_of_twoThreeUnitBound hSUnit D with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro A B k r u x y hBlock hSource hTarget hAB
  have hSparseAB : SparseEndpointComplementsAtMost u y (A + B) :=
    sparseEndpointComplementsAtMost_of_sourceTargetDefect
      hBlock hSource hTarget
  have hSparseD : SparseEndpointComplementsAtMost u y D :=
    hSparseAB.mono hAB
  rcases exists_exactBlockSparseEquation_of_sparseComplements hBlock hSparseD with
    ⟨sourceLength, targetLength, sourceTail, targetBits, hEq, hCount⟩
  exact hK k sourceLength r targetLength sourceTail targetBits hEq hCount

/--
十分深い block では、exact source/target defect の合計は任意の固定 `D` を超える。

これは `defect is unbounded` を source/target の total defect として明示した形。
-/
theorem deepBlock_forces_totalDefect_above_bound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (D : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y sourceDefect sourceLength targetDefect targetLength : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefect x sourceDefect sourceLength →
        Binary.HasZeroDefect y targetDefect targetLength →
        K ≤ k →
        D < sourceDefect + targetDefect := by
  rcases exists_depth_bound_of_totalDefect hSUnit D with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y sourceDefect sourceLength targetDefect targetLength
    hBlock hSource hTarget hk
  by_contra hNot
  have hSum : sourceDefect + targetDefect ≤ D := by
    omega
  have hSourceAtMost : Binary.HasZeroDefectAtMost x sourceDefect :=
    Binary.HasZeroDefectAtMost.of_exact hSource (by omega)
  have hTargetAtMost : Binary.HasZeroDefectAtMost y targetDefect :=
    Binary.HasZeroDefectAtMost.of_exact hTarget (by omega)
  have hkLt : k < K :=
    hK sourceDefect targetDefect k r u x y
      hBlock hSourceAtMost hTargetAtMost hSum
  omega

/--
source defect が正なら coefficient 側で1 hole 減ることまで使った sharpened qualitative 版。

十分深い block では

`D + 1 < sourceDefect + targetDefect`

となる。
-/
theorem deepBlock_forces_exact_totalDefect_above_succ
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (D : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y sourceDefect sourceLength targetDefect targetLength : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefect x sourceDefect sourceLength →
        Binary.HasZeroDefect y targetDefect targetLength →
        0 < sourceDefect →
        K ≤ k →
        D + 1 < sourceDefect + targetDefect := by
  rcases blockSparsePow3Escape_of_twoThreeUnitBound hSUnit D with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y sourceDefect sourceLength targetDefect targetLength
    hBlock hSource hTarget hSourcePos hk
  by_contra hNot
  have hSum : sourceDefect + targetDefect ≤ D + 1 := by
    omega
  have hHole : (sourceDefect - 1) + targetDefect ≤ D := by
    omega
  have hSparse :=
    sparseEndpointComplementsAtMost_of_exact_sourceTarget
      hBlock hSource hTarget hSourcePos
  have hSparseD : SparseEndpointComplementsAtMost u y D :=
    hSparse.mono hHole
  rcases exists_exactBlockSparseEquation_of_sparseComplements hBlock hSparseD with
    ⟨sourceLength', targetLength', sourceTail, targetBits, hEq, hCount⟩
  have hkLt : k < K :=
    hK k sourceLength' r targetLength' sourceTail targetBits hEq hCount
  omega

end Mersenne
end Collatz3
