import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDirectEndpointResidue
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftRecordFerrersResidualIncompatibility
set_option linter.style.longLine false
/-!
# 第3例探索 6: 右 endpoint 復元とは独立な RecordFerrers residual 条件

右 `3^42` compatibility は endpoint を一意に復元するだけなので、それ単独では排除にならない。
独立条件として、既存の left RecordFerrers residual incompatibility を finite kernel へ公開する。

actual identification が成立すれば、left residual は 3-adic unit である一方、
coarsening carry residual は exact に3の倍数なので矛盾する。
-/

namespace Collatz2
namespace CSTMicro
open ExternalArithmetic
namespace ThirdExampleSearch

open MultiCorner
open Collatz2.Word

/--
proof-free candidate に付加できる独立 Bool checker の型。
右 endpoint 復元器とは完全に分離する。
-/
abbrev ThirdExampleIndependentCandidateChecker :=
  ThirdExampleBranchDeficitCandidate → Bool

/-- checker が候補を受理するという軽量 predicate。 -/
def ThirdExampleIndependentCandidateAccepted
    (check : ThirdExampleIndependentCandidateChecker)
    (C : ThirdExampleBranchDeficitCandidate) : Prop :=
  check C = true

/--
既存 Case II residual incompatibility の直接 wrapper。
この theorem により、finite local state から `hIdentify` を供給できれば即座に False へ落ちる。
-/
theorem thirdExampleFalse_of_leftResidualIdentification
    {P : PureBProfileObstruction}
    (B : LeftOfCriticalizationBridge P)
    {w : Word}
    (D : RankRecordDecomposition w B.left.index)
    (H : ℕ)
    (h : ℕ → ℕ)
    {kappa : ℕ}
    (hA :
      D.profileBlockCostQuotientSumFrom H h =
        columnProfileCostQuotientInterval
            H (Word.oddSteps w) h B.left.index D.lengths.sum +
          kappa)
    (hIdentify :
      B.leftResidual =
        D.lambdaCoarseningCarryResidualZFrom H h) :
    False := by
  exact
    MultiCorner.LeftOfCriticalizationBridge.false_of_leftResidual_eq_lambdaCoarseningCarryResidualZFrom
      B D H h hA hIdentify

end ThirdExampleSearch
end CSTMicro
end Collatz2
