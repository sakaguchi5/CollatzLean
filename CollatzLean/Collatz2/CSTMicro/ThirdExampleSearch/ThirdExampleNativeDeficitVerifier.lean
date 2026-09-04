import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitSoundness
set_option linter.style.nativeDecide false
/-!
# 第3例探索: native_decide の最終ターゲット

このファイルでは有限計算だけを行う。
数学側の exact soundness は前段に隔離する。

現在 repo にまだ必要なのは、全12,341枝について
`ThirdExampleFiniteDeficitRow` を作る concrete table である。
その table が入れば `thirdExampleFiniteDeficitSurvivors = []` を `native_decide` するだけになる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- finite branch domain 自体はすでに native evaluator だけで exact に確定する。 -/
theorem thirdExampleNativeFiniteBranchCount :
    thirdExampleFiniteDeficitBranches.length = 12_341 := by
  native_decide

/--
concrete table の branch 列が完全有限 domain と一致することを計算で確認する predicate。
-/
def thirdExampleFiniteDeficitTableHasCompleteDomain
    (table : List ThirdExampleFiniteDeficitRow) : Bool :=
  decide (table.map (fun R => R.branch) = thirdExampleFiniteDeficitBranches)

/--
最終 `native_decide` の形を固定する。
concrete table と D2 packet を与えれば、survivor の空判定は完全に計算問題になる。
-/
def thirdExampleFiniteDeficitVerifierAccepts
    (D : ThirdExampleD2FinitePacket)
    (table : List ThirdExampleFiniteDeficitRow) : Bool :=
  thirdExampleFiniteDeficitTableHasCompleteDomain table &&
    (thirdExampleFiniteDeficitSurvivors D table).isEmpty

/-- 空 table は complete domain ではないので、誤って証明を閉じない。 -/
theorem thirdExampleEmptyDeficitTable_rejected
    (D : ThirdExampleD2FinitePacket) :
    thirdExampleFiniteDeficitVerifierAccepts D [] = false := by
  have hDomain :
      thirdExampleFiniteDeficitTableHasCompleteDomain [] = false := by
    decide
  unfold thirdExampleFiniteDeficitVerifierAccepts
  rw [hDomain]
  rfl

end ThirdExampleSearch
end CSTMicro
end Collatz2
