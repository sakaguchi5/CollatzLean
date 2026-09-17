import CollatzLean.Collatz3.Binary.Defect

/-!
# Collatz3 Binary: bounded zero defect

exact zero defect `HasZeroDefect` から、上限だけを忘れた薄い predicate を作る。

新しい binary representation は導入しない。
後段の Mersenne obstruction では「出口の `0` 個数が固定上限以下」という条件だけを
この predicate で受け取る。
-/

namespace Collatz3
namespace Binary

/-- 自然数 `x` は、ある固定長 binary representation で zero defect が `bound` 以下。 -/
def HasZeroDefectAtMost (x bound : ℕ) : Prop :=
  ∃ defect length : ℕ,
    HasZeroDefect x defect length ∧ defect ≤ bound

namespace HasZeroDefectAtMost

/-- exact defect から bounded defect を得る。 -/
theorem of_exact
    {x defect length bound : ℕ}
    (h : HasZeroDefect x defect length)
    (hLe : defect ≤ bound) :
    HasZeroDefectAtMost x bound := by
  exact ⟨defect, length, h, hLe⟩

/-- defect 上限を大きくしても bounded defect は保存される。 -/
theorem mono
    {x a b : ℕ}
    (h : HasZeroDefectAtMost x a)
    (hab : a ≤ b) :
    HasZeroDefectAtMost x b := by
  rcases h with ⟨defect, length, hDefect, hLe⟩
  exact ⟨defect, length, hDefect, le_trans hLe hab⟩

end HasZeroDefectAtMost

end Binary
end Collatz3
