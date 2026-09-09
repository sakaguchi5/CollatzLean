import CollatzLean.Collatz3.Experimental2.FiniteComposition

/-!
# Collatz3 Experimental2: normalized Record 型 budget の便利な corollary

kernel では一般 anchor の factorization budget だけを正本とする。
ここでは旧 Experimental で便利だった normalized anchor `1` の結論を derived wrapper として戻す。
-/

namespace Collatz3
namespace Experimental2

namespace HasUnitCarry

/-- 最後が carry `0` で total budget が最大なら carry 列は `1,...,1,0`。 -/
theorem carryListFrom_append_singleton_eq_ones_then_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (pre : List ℕ)
    (r : ℕ)
    (hLastZero : roofCarry β (a + pre.sum) r = 0)
    (hTotal :
      (carryListFrom β a (pre ++ [r])).sum = pre.length) :
    carryListFrom β a (pre ++ [r]) =
      List.replicate pre.length 1 ++ [0] := by
  have hAppend := carryListFrom_append (β := β) a pre [r]
  rw [hAppend] at hTotal
  have hPreMax : (carryListFrom β a pre).sum = pre.length := by
    simpa [carryListFrom, hLastZero] using hTotal
  have hPreOnes :=
    U.carryListFrom_eq_replicate_one_of_sum_eq_length a pre hPreMax
  rw [carryListFrom_append (β := β) a pre [r]]
  simp [carryListFrom, hLastZero, hPreOnes]

/-- normalized anchor `1`, `β(1)=1` の factorization は budget `length-1` を強制する。 -/
theorem normalizedFactorization_carrySum_eq_length_sub_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (rs : List ℕ)
    (hCover : m = 1 + rs.sum)
    (hFactor : β m = (rs.map β).sum + rs.length) :
    (carryListFrom β 1 rs).sum = rs.length - 1 := by
  have hBudget :=
    U.factorization_anchor_add_carrySum_eq_budget
      (a := 1) (K := rs.length) rs hCover hFactor
  rw [hOne] at hBudget
  omega

/-- 非空 normalized factorization では carry `0` が exact に一個。 -/
theorem normalizedFactorization_forces_uniqueZeroCount
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (rs : List ℕ)
    (hNonempty : rs ≠ [])
    (hCover : m = 1 + rs.sum)
    (hFactor : β m = (rs.map β).sum + rs.length) :
    (carryListFrom β 1 rs).count 0 = 1 := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne rs hCover hFactor
  have H :=
    U.carryListFrom_isBitList 1 rs
  have hCarryNonempty :
      carryListFrom β 1 rs ≠ [] := by
    intro hEmpty
    have hLen :
        (carryListFrom β 1 rs).length = rs.length :=
      carryListFrom_length (β := β) 1 rs
    rw [hEmpty] at hLen
    simp at hLen
    apply hNonempty
    exact List.length_eq_zero_iff.mp hLen.symm
  have hBudgetLen :
      (carryListFrom β 1 rs).sum =
        (carryListFrom β 1 rs).length - 1 := by
    simpa using hBudget
  exact
    H.count_zero_eq_one_of_sum_eq_length_sub_one
      hCarryNonempty hBudgetLen

/-- terminal carry `0` を加えると canonical pattern は `1,...,1,0` に一意化される。 -/
theorem normalizedFactorization_forces_ones_then_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (pre : List ℕ)
    (r : ℕ)
    (hCover : m = 1 + (pre ++ [r]).sum)
    (hFactor :
      β m = ((pre ++ [r]).map β).sum + (pre ++ [r]).length)
    (hLastZero : roofCarry β (1 + pre.sum) r = 0) :
    carryListFrom β 1 (pre ++ [r]) =
      List.replicate pre.length 1 ++ [0] := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne (pre ++ [r]) hCover hFactor
  have hTotal :
      (carryListFrom β 1 (pre ++ [r])).sum = pre.length := by
    simpa using hBudget
  exact U.carryListFrom_append_singleton_eq_ones_then_zero
    1 pre r hLastZero hTotal

/-- proper prefix 部分の carry は全て `1`。 -/
theorem normalizedFactorization_prefixCarries_eq_replicate_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (pre : List ℕ)
    (r : ℕ)
    (hCover : m = 1 + (pre ++ [r]).sum)
    (hFactor :
      β m = ((pre ++ [r]).map β).sum + (pre ++ [r]).length)
    (hLastZero : roofCarry β (1 + pre.sum) r = 0) :
    carryListFrom β 1 pre = List.replicate pre.length 1 := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne (pre ++ [r]) hCover hFactor
  have hAppend := carryListFrom_append (β := β) 1 pre [r]
  rw [hAppend] at hBudget
  have hPreMax : (carryListFrom β 1 pre).sum = pre.length := by
    simpa [carryListFrom, hLastZero] using hBudget
  exact U.carryListFrom_eq_replicate_one_of_sum_eq_length 1 pre hPreMax

end HasUnitCarry
end Experimental2
end Collatz3
