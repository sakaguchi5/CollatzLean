import CollatzLean.Collatz3.CSTCarry.CarryBudgetTelescopeProgram

/-!
# Collatz3 CSTCarry: CarryRealizes の append 合成

block budget telescope を実際の carry chain に接続するため、
二つの `CarryRealizes` を中間 carry で連結する。
-/

namespace Collatz3
namespace CSTCarry

namespace CarryRealizes

/--
二つの carry realization は共通の中間 carry で exact に append できる。
-/
theorem append
    {M : ℕ}
    {rows₀ rows₁ : List FerrersRow}
    {E K F : ℕ}
    {digits₀ digits₁ : List ℕ}
    (h₀ : CarryRealizes M rows₀ E digits₀ K)
    (h₁ : CarryRealizes M rows₁ K digits₁ F) :
    CarryRealizes M (rows₀ ++ rows₁) E (digits₀ ++ digits₁) F := by
  induction h₀ generalizing rows₁ digits₁ F with
  | nil E =>
      simpa using h₁
  | cons R Rs E a E' K digits ha hEq hTail ih =>
      simp only [List.cons_append]
      exact CarryRealizes.cons
        R (Rs ++ rows₁) E a E' F (digits ++ digits₁)
        ha hEq (ih h₁)

end CarryRealizes

end CSTCarry
end Collatz3
