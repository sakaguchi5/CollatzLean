import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleBranchLocalDeficitCandidates

/-!
# 第3例探索 4: exact 3-adic order filter

actual criticalization depth は `r+d = p-s`。
`r+d <= 41` なので、`mod 3^42` の canonical representative だけで

  3^(r+d) | deficit
  3^(r+d+1) ∤ deficit

を lossless に検査できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- Nat representative 上の exact 3-adic order checker。 -/
def thirdExampleDeficitHasBranchOrder
    (C : ThirdExampleBranchDeficitCandidate) : Bool :=
  let depth := C.branch.r + C.branch.d
  decide
    (C.deficit.val % (3 ^ depth) = 0 ∧
      C.deficit.val % (3 ^ (depth + 1)) ≠ 0)

/-- exact-order filter を通過した candidate だけ残す。 -/
def thirdExampleThreeAdicFilteredCandidates
    (G : ThirdExampleBranchDeficitGenerator) :
    List ThirdExampleBranchDeficitCandidate :=
  (thirdExampleBranchDeficitCandidates G).filter
    thirdExampleDeficitHasBranchOrder

/-- checker の意味を Prop へ戻す exact iff。 -/
theorem thirdExampleDeficitHasBranchOrder_eq_true_iff
    (C : ThirdExampleBranchDeficitCandidate) :
    thirdExampleDeficitHasBranchOrder C = true ↔
      C.deficit.val % (3 ^ (C.branch.r + C.branch.d)) = 0 ∧
        C.deficit.val % (3 ^ (C.branch.r + C.branch.d + 1)) ≠ 0 := by
  simp [thirdExampleDeficitHasBranchOrder]

/-- finite branch では order test に必要な一段深い指数も42以下。 -/
theorem thirdExampleBranch_order_succ_le_42
    {B : ThirdExampleRDW}
    (hB : ThirdExampleFiniteDeficitBranch B) :
    B.r + B.d + 1 ≤ 42 := by
  exact Nat.succ_le_succ hB.1

end ThirdExampleSearch
end CSTMicro
end Collatz2
