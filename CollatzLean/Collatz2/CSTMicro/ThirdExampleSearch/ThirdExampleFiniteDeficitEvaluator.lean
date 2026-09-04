import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueD2Aggregate
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitBranch

/-!
# 第3例探索: proof-free finite deficit compatibility evaluator

D2 の full-defect residue / endpoint residue と、branch ごとの Ferrers deficit residue を
一つの `Bool` 判定へ落とす。

このファイルは数学証明を runtime state に持ち込まない。
`deficitResidue` は次の soundness 層で actual Ferrers deficit と一致することを証明する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- target の critical roof exponent `β = H-1` を計算用 literal として使う。 -/
def thirdExampleTargetBeta : ℕ :=
  thirdExampleTargetH - 1

/--
一枝の deficit residue を与える proof-free table row。
`branch` と residue だけを保持し、巨大 exact integer は持たない。
-/
@[ext]
structure ThirdExampleFiniteDeficitRow where
  branch : ThirdExampleRDW
  deficitModThree : ZMod thirdExampleRightModulus
  deriving DecidableEq

/--
full defect / endpoint / branch deficit の affine compatibility を判定する。

  2^β (endpoint+1) = 2 (fullDefect-deficit)  (mod 3^42)
-/
def thirdExampleFiniteDeficitCompatible
    (D : ThirdExampleD2FinitePacket)
    (deficitModThree : ZMod thirdExampleRightModulus) : Bool :=
  decide
    (((2 : ZMod thirdExampleRightModulus) ^ thirdExampleTargetBeta) *
        ((D.endpointModThree : ZMod thirdExampleRightModulus) + 1) =
      2 *
        (D.defectState.fullDefectModThree - deficitModThree))

/-- table row 一本に対する compatibility。 -/
def thirdExampleFiniteDeficitRowCompatible
    (D : ThirdExampleD2FinitePacket)
    (R : ThirdExampleFiniteDeficitRow) : Bool :=
  thirdExampleFiniteDeficitCompatible D R.deficitModThree

/--
有限 deficit table から compatibility survivor だけを残す hot-path evaluator。
-/
def thirdExampleFiniteDeficitSurvivors
    (D : ThirdExampleD2FinitePacket)
    (table : List ThirdExampleFiniteDeficitRow) :
    List ThirdExampleFiniteDeficitRow :=
  table.filter (thirdExampleFiniteDeficitRowCompatible D)

/-- Bool 判定を theorem 側で使うための exact iff。 -/
theorem thirdExampleFiniteDeficitCompatible_eq_true_iff
    (D : ThirdExampleD2FinitePacket)
    (deficitModThree : ZMod thirdExampleRightModulus) :
    thirdExampleFiniteDeficitCompatible D deficitModThree = true ↔
      ((2 : ZMod thirdExampleRightModulus) ^ thirdExampleTargetBeta) *
          ((D.endpointModThree : ZMod thirdExampleRightModulus) + 1) =
        2 *
          (D.defectState.fullDefectModThree - deficitModThree) := by
  simp [thirdExampleFiniteDeficitCompatible]

end ThirdExampleSearch
end CSTMicro
end Collatz2
