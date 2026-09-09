import CollatzLean.Collatz3.Experimental.CarryCocycle

/-!
# Collatz3 experimental: Record 型 factorization が強制する carry budget

現行 `RecordFerrers` を import せず、その算術 factorization の形だけを抽象的に仮定して
carry 列に何が強制されるかを調べる。

normalized anchor `1`、`β(1)=1`、

`m = 1 + Σ rᵢ`
`β(m) = Σ β(rᵢ) + numberOfBlocks`

が成立すると、有限 block 合成の exact equation から
carry 総和は `numberOfBlocks - 1` に強制される。
さらに最後の carry が `0` なら、全境界 carry は exact に

`1, ..., 1, 0`

となる。
-/

namespace Collatz3
namespace Experimental

namespace HasUnitCarry

/--
normalized anchor `1` を持つ Record 型 roof factorization は、
carry 総和を exact に `block数 - 1` へ固定する。
-/
theorem normalizedFactorization_carrySum_eq_length_sub_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (rs : List ℕ)
    (hCover : m = 1 + rs.sum)
    (hFactor :
      β m = (rs.map β).sum + rs.length) :
    (carryListFrom β 1 rs).sum = rs.length - 1 := by
  have hExact :=
    U.roof_add_sum_eq_blockRoofs_add_carries 1 rs
  rw [← hCover, hOne] at hExact
  omega

/--
Record 型 factorization に terminal carry `0` を追加すると、
全 canonical boundary carry の形は `1, ..., 1, 0` に一意化される。

ここでは record cut や Ferrers geometry は一切仮定していない。
必要なのは roof factorization と terminal carry だけ。
-/
theorem normalizedFactorization_forces_ones_then_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (pre : List ℕ)
    (r : ℕ)
    (hCover : m = 1 + (pre ++ [r]).sum)
    (hFactor :
      β m =
        ((pre ++ [r]).map β).sum +
          (pre ++ [r]).length)
    (hLastZero :
      roofCarry β (1 + pre.sum) r = 0) :
    carryListFrom β 1 (pre ++ [r]) =
      List.replicate pre.length 1 ++ [0] := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne (pre ++ [r]) hCover hFactor
  have hTotal :
      (carryListFrom β 1 (pre ++ [r])).sum = pre.length := by
    simpa using hBudget
  exact
    U.carryListFrom_append_singleton_eq_ones_then_zero
      1 pre r hLastZero hTotal

/--
上の結論から、proper boundary 部分だけを切り出すと carry は全て `1`。
-/
theorem normalizedFactorization_prefixCarries_eq_replicate_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (pre : List ℕ)
    (r : ℕ)
    (hCover : m = 1 + (pre ++ [r]).sum)
    (hFactor :
      β m =
        ((pre ++ [r]).map β).sum +
          (pre ++ [r]).length)
    (hLastZero :
      roofCarry β (1 + pre.sum) r = 0) :
    carryListFrom β 1 pre =
      List.replicate pre.length 1 := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne (pre ++ [r]) hCover hFactor
  have hAppend :=
    carryListFrom_append (β := β) 1 pre [r]
  rw [hAppend] at hBudget
  have hPreMax :
      (carryListFrom β 1 pre).sum = pre.length := by
    simpa [carryListFrom, hLastZero] using hBudget
  exact
    U.carryListFrom_eq_replicate_one_of_sum_eq_length
      1 pre hPreMax

end HasUnitCarry
end Experimental
end Collatz3
