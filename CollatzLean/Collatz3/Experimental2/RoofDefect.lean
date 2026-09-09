import CollatzLean.Collatz3.Experimental2.FiniteComposition
import CollatzLean.Collatz3.Experimental2.Normalization

/-!
# Collatz3 Experimental2: global roof defect

有限 block factorization の余剰を `roofDefect` として読む derived view。
defect は carry 総和であり、block permutation・二分 split・正規化に対して自然な保存則を持つ。
-/

namespace Collatz3
namespace Experimental2

/-- start `a` と block 列 `rs` に対する global additive defect。 -/
def roofDefect
    (β : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) : ℕ :=
  β (a + rs.sum) - (β a + (rs.map β).sum)

/-- 自然数リストの和は permutation で不変。 -/
theorem list_sum_eq_of_perm
    {xs ys : List ℕ}
    (hPerm : xs.Perm ys) :
    xs.sum = ys.sum := by
  induction hPerm with
  | nil => rfl
  | cons x hPerm ih => simp [ih]
  | swap x y xs => simp only [List.sum_cons, Nat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

namespace HasUnitCarry

/-- global defect は carry 総和そのもの。 -/
theorem roofDefect_eq_carrySum
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    roofDefect β a rs = (carryListFrom β a rs).sum := by
  have h := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  unfold roofDefect
  omega

/-- defect は block 数以下。 -/
theorem roofDefect_le_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    roofDefect β a rs ≤ rs.length := by
  rw [U.roofDefect_eq_carrySum]
  exact U.carryListFrom_sum_le_length a rs

/-- 正規化しても有限 carry 列は変わらない。 -/
theorem carryListFrom_normalizeRoof_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ a rs,
      carryListFrom (normalizeRoof β) a rs = carryListFrom β a rs
  | _a, [] => by simp [carryListFrom]
  | a, r :: rs => by
      simp [carryListFrom, U.roofCarry_normalizeRoof_eq,
        U.carryListFrom_normalizeRoof_eq (a + r) rs]

/-- global defect も正規化で完全に保存される。 -/
theorem roofDefect_normalizeRoof_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    roofDefect (normalizeRoof β) a rs = roofDefect β a rs := by
  rw [(U.normalizeRoof_hasUnitCarry).roofDefect_eq_carrySum,
    U.roofDefect_eq_carrySum]
  rw [U.carryListFrom_normalizeRoof_eq]

end HasUnitCarry

/-- block 長を permutation しても global defect は変わらない。 -/
theorem roofDefect_eq_of_perm
    {β : ℕ → ℕ}
    (a : ℕ)
    {rs ts : List ℕ}
    (hPerm : rs.Perm ts) :
    roofDefect β a rs = roofDefect β a ts := by
  have hWidth : rs.sum = ts.sum := list_sum_eq_of_perm hPerm
  have hRoofPerm : (rs.map β).Perm (ts.map β) := hPerm.map β
  have hRoofSum : (rs.map β).sum = (ts.map β).sum :=
    list_sum_eq_of_perm hRoofPerm
  simp [roofDefect, hWidth, hRoofSum]

namespace HasUnitCarry

/-- unit-carry の下では carry 総和も permutation で不変。 -/
theorem carrySum_eq_of_perm
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    {rs ts : List ℕ}
    (hPerm : rs.Perm ts) :
    (carryListFrom β a rs).sum = (carryListFrom β a ts).sum := by
  rw [← U.roofDefect_eq_carrySum, ← U.roofDefect_eq_carrySum]
  exact roofDefect_eq_of_perm a hPerm

/-- `b+d` を `b,d` に split すると defect は `c(b,d)` だけ増える。 -/
theorem roofDefect_split_two
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b d : ℕ) :
    roofDefect β a [b + d] + roofCarry β b d =
      roofDefect β a [b, d] := by
  rw [U.roofDefect_eq_carrySum, U.roofDefect_eq_carrySum]
  simp only [carryListFrom, List.sum_cons, List.sum_nil, Nat.add_zero]
  have h := U.carry_cocycle a b d
  omega

end HasUnitCarry
end Experimental2
end Collatz3
