import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleIndependentResidualFilter
set_option linter.style.nativeDecide false

/-!
# 第3例探索 7: 最終 native_decide kernel

このファイルでは数学証明を runtime state から外し、

1. 全12,341枝を展開
2. branch-local deficit candidates を flatMap
3. exact 3-adic order filter
4. 独立 checker

だけを計算する。

重要:
branch-local generator と independent checker の actual completeness/soundness は proof-side の責務。
空 generator や常時 false checker を「第3例不存在」と誤認しないよう、kernel は
complete-domain witness を別に要求する設計にする。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 最終 runtime survivor。endpoint residue も一緒に保持する。 -/
@[ext]
structure ThirdExampleFinalFiniteSurvivor where
  candidate : ThirdExampleBranchDeficitCandidate
  endpointModThree : ZMod thirdExampleRightModulus
  deriving DecidableEq

/-- 3-adic filter 後に independent checker を掛ける。 -/
def thirdExampleFinalCandidates
    (G : ThirdExampleBranchDeficitGenerator)
    (check : ThirdExampleIndependentCandidateChecker) :
    List ThirdExampleBranchDeficitCandidate :=
  (thirdExampleThreeAdicFilteredCandidates G).filter check

/-- endpoint residue を復元して最終 survivor packet にする。 -/
def thirdExampleFinalSurvivors
    (G : ThirdExampleBranchDeficitGenerator)
    (check : ThirdExampleIndependentCandidateChecker) :
    List ThirdExampleFinalFiniteSurvivor :=
  (thirdExampleFinalCandidates G check).map (fun C =>
    {
      candidate := C
      endpointModThree := thirdExampleEndpointResidueOfDeficit C.deficit
    })

/--
最終 `native_decide` が評価する Bool。
具体 generator/checker が入った段階ではこの値を `true` と証明すればよい。
-/
def thirdExampleFinalNativeRejectsAll
    (G : ThirdExampleBranchDeficitGenerator)
    (check : ThirdExampleIndependentCandidateChecker) : Bool :=
  (thirdExampleFinalSurvivors G check).isEmpty

/-- 母集合12,341枝は最終 kernel でも固定。 -/
theorem thirdExampleFinalNativeBranchCount :
    thirdExampleFiniteDeficitBranches.length = 12_341 := by
  native_decide

/--
具体的 generator/checker に対する最終証明の標準形。
`hNative` は concrete definitions に対して `by native_decide` で供給する。
-/
theorem thirdExampleFinalSurvivors_eq_nil_of_native
    (G : ThirdExampleBranchDeficitGenerator)
    (check : ThirdExampleIndependentCandidateChecker)
    (hNative : thirdExampleFinalNativeRejectsAll G check = true) :
    thirdExampleFinalSurvivors G check = [] := by
  unfold thirdExampleFinalNativeRejectsAll at hNative
  generalize hList : thirdExampleFinalSurvivors G check = xs at hNative ⊢
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      simp at hNative

end ThirdExampleSearch
end CSTMicro
end Collatz2
