import CollatzLean.Collatz3.Experimental2.CarryCore
import CollatzLean.Collatz3.Experimental2.BitList

/-!
# Collatz3 Experimental2: 有限 block 合成と carry budget

block 列から carry 列を有限再帰で計算し、
global factorization の余剰が carry 総和そのものになることを証明する。
-/

namespace Collatz3
namespace Experimental2

/-- start `a` から block 列を順に結合した carry 列。 -/
def carryListFrom
    (β : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _a, [] => []
  | a, r :: rs =>
      roofCarry β a r :: carryListFrom β (a + r) rs

@[simp] theorem carryListFrom_length
    {β : ℕ → ℕ} :
    ∀ a rs, (carryListFrom β a rs).length = rs.length
  | _a, [] => by simp [carryListFrom]
  | a, r :: rs => by
      simp [carryListFrom, carryListFrom_length (β := β) (a + r) rs]

theorem carryListFrom_append
    {β : ℕ → ℕ} :
    ∀ a xs ys,
      carryListFrom β a (xs ++ ys) =
        carryListFrom β a xs ++
          carryListFrom β (a + xs.sum) ys
  | _a, [], ys => by simp [carryListFrom]
  | a, r :: rs, ys => by
      simp [carryListFrom,
        carryListFrom_append (β := β) (a + r) rs ys,
        Nat.add_assoc]

namespace HasUnitCarry

/-- carry 列は bit list。 -/
theorem carryListFrom_isBitList
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    IsBitList (carryListFrom β a rs) := by
  intro c hc
  induction rs generalizing a with
  | nil =>
      simp [carryListFrom] at hc
  | cons r rs ih =>
      simp only [carryListFrom, List.mem_cons] at hc
      rcases hc with h | h
      · subst c
        exact U.carry_le_one a r
      · exact ih (a := a + r) h

/-- carry 総和は block 数以下。 -/
theorem carryListFrom_sum_le_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    (carryListFrom β a rs).sum ≤ rs.length := by
  have H := U.carryListFrom_isBitList a rs
  simpa using H.sum_le_length

/-- 有限 block 合成の exact equation。 -/
theorem roof_add_sum_eq_blockRoofs_add_carries
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ a rs,
      β (a + rs.sum) =
        β a + (rs.map β).sum + (carryListFrom β a rs).sum
  | a, [] => by simp [carryListFrom]
  | a, r :: rs => by
      have hHead := U.add_eq a r
      have hTail :=
        U.roof_add_sum_eq_blockRoofs_add_carries (a + r) rs
      simp only [List.sum_cons, List.map_cons, carryListFrom]
      have hIndex : a + (r + rs.sum) = (a + r) + rs.sum := by omega
      rw [hIndex]
      omega

/-- 一般 factorization の余剰 `K` は carry 総和。 -/
theorem factorization_carryBudget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a m K : ℕ}
    (rs : List ℕ)
    (hCover : m = a + rs.sum)
    (hFactor : β m = β a + (rs.map β).sum + K) :
    (carryListFrom β a rs).sum = K := by
  have hExact := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  rw [← hCover] at hExact
  omega

/-- anchor を factorization 右辺に書かない場合の一般 budget。 -/
theorem factorization_anchor_add_carrySum_eq_budget
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a m K : ℕ}
    (rs : List ℕ)
    (hCover : m = a + rs.sum)
    (hFactor : β m = (rs.map β).sum + K) :
    β a + (carryListFrom β a rs).sum = K := by
  have hExact := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  rw [← hCover] at hExact
  omega

/-- 最大 carry budget なら全 carry は `1`。 -/
theorem carryListFrom_eq_replicate_one_of_sum_eq_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ)
    (hMax : (carryListFrom β a rs).sum = rs.length) :
    carryListFrom β a rs = List.replicate rs.length 1 := by
  have H := U.carryListFrom_isBitList a rs
  have hSumLen :
      (carryListFrom β a rs).sum =
        (carryListFrom β a rs).length := by
    simpa using hMax
  have hAll :=
    H.eq_replicate_one_of_sum_eq_length hSumLen
  simpa using hAll

end HasUnitCarry
end Experimental2
end Collatz3
