import CollatzLean.Collatz3.Mersenne.SmallHoleExact
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination


/-!
# Collatz3 Mersenne: boundary-hole peel

最上位 hole は一つ短い Mersenne word に吸収できる。
既存の `n=2` 専用 bridge を一般の top-hole reduction としてまとめる。
-/

namespace Collatz3
namespace Mersenne

/-- source-one の最上位 hole は no-hole へ落ちる。 -/
theorem SourceOneHoleEquation.top_hole_to_noHole
    {k n r L : ℕ}
    (hn : 0 < n)
    (hEq : SourceOneHoleEquation k n r L (n - 1)) :
    NoHoleEquation k (n - 1) r L := by
  unfold SourceOneHoleEquation at hEq
  unfold NoHoleEquation
  have hnEq : n = (n - 1) + 1 := by
    omega
  have hPowN :
      (2 : ℤ) ^ n =
        (2 : ℤ) ^ (n - 1) * 2 := by
    calc
      (2 : ℤ) ^ n =
          (2 : ℤ) ^ ((n - 1) + 1) := by
            rw [hnEq]
            simp
      _ = (2 : ℤ) ^ (n - 1) * 2 := by
            rw [pow_succ]
  rw [hPowN] at hEq
  linear_combination hEq


/-- target-one の最上位 hole は no-hole へ落ちる。 -/
theorem TargetOneHoleEquation.top_hole_to_noHole
    {k n r L : ℕ}
    (hL : 0 < L)
    (hEq : TargetOneHoleEquation k n r L (L - 1)) :
    NoHoleEquation k n r (L - 1) := by
  unfold TargetOneHoleEquation at hEq
  unfold NoHoleEquation
  have hLEq : L = (L - 1) + 1 := by
    omega
  have hPowL :
      (2 : ℤ) ^ L =
        (2 : ℤ) ^ (L - 1) * 2 := by
    calc
      (2 : ℤ) ^ L =
          (2 : ℤ) ^ ((L - 1) + 1) := by
            rw [hLEq]
            simp
      _ = (2 : ℤ) ^ (L - 1) * 2 := by
            rw [pow_succ]
  rw [hPowL] at hEq
  linear_combination hEq


/-- source-two の後ろの top hole を peel すると source-one。 -/
theorem SourceTwoHoleEquation.second_top_hole_to_sourceOne
    {k n r L a : ℕ}
    (hn : 0 < n)
    (hEq : SourceTwoHoleEquation k n r L a (n - 1)) :
    SourceOneHoleEquation k (n - 1) r L a := by
  unfold SourceTwoHoleEquation at hEq
  unfold SourceOneHoleEquation
  have hnEq : n = (n - 1) + 1 := by
    omega
  have hPowN :
      (2 : ℤ) ^ n =
        (2 : ℤ) ^ (n - 1) * 2 := by
    calc
      (2 : ℤ) ^ n =
          (2 : ℤ) ^ ((n - 1) + 1) := by
            rw [hnEq]
            simp
      _ = (2 : ℤ) ^ (n - 1) * 2 := by
            rw [pow_succ]
  rw [hPowN] at hEq
  linear_combination hEq


/-- target-two の後ろの top hole を peel すると target-one。 -/
theorem TargetTwoHoleEquation.second_top_hole_to_targetOne
    {k n r L a : ℕ}
    (hL : 0 < L)
    (hEq : TargetTwoHoleEquation k n r L a (L - 1)) :
    TargetOneHoleEquation k n r (L - 1) a := by
  unfold TargetTwoHoleEquation at hEq
  unfold TargetOneHoleEquation
  have hLEq : L = (L - 1) + 1 := by
    omega
  have hPowL :
      (2 : ℤ) ^ L =
        (2 : ℤ) ^ (L - 1) * 2 := by
    calc
      (2 : ℤ) ^ L =
          (2 : ℤ) ^ ((L - 1) + 1) := by
            rw [hLEq]
            simp
      _ = (2 : ℤ) ^ (L - 1) * 2 := by
            rw [pow_succ]
  rw [hPowL] at hEq
  linear_combination hEq


/-- split-two の source top hole を peel すると target-one。 -/
theorem SplitTwoHoleEquation.source_top_hole_to_targetOne
    {k n r L b : ℕ}
    (hn : 0 < n)
    (hEq : SplitTwoHoleEquation k n r L (n - 1) b) :
    TargetOneHoleEquation k (n - 1) r L b := by
  unfold SplitTwoHoleEquation at hEq
  unfold TargetOneHoleEquation
  have hnEq : n = (n - 1) + 1 := by
    omega
  have hPowN :
      (2 : ℤ) ^ n =
        (2 : ℤ) ^ (n - 1) * 2 := by
    calc
      (2 : ℤ) ^ n =
          (2 : ℤ) ^ ((n - 1) + 1) := by
            rw [hnEq]
            simp
      _ = (2 : ℤ) ^ (n - 1) * 2 := by
            rw [pow_succ]
  rw [hPowN] at hEq
  linear_combination hEq


/-- split-two の target top hole を peel すると source-one。 -/
theorem SplitTwoHoleEquation.target_top_hole_to_sourceOne
    {k n r L a : ℕ}
    (hL : 0 < L)
    (hEq : SplitTwoHoleEquation k n r L a (L - 1)) :
    SourceOneHoleEquation k n r (L - 1) a := by
  unfold SplitTwoHoleEquation at hEq
  unfold SourceOneHoleEquation
  have hLEq : L = (L - 1) + 1 := by
    omega
  have hPowL :
      (2 : ℤ) ^ L =
        (2 : ℤ) ^ (L - 1) * 2 := by
    calc
      (2 : ℤ) ^ L =
          (2 : ℤ) ^ ((L - 1) + 1) := by
            rw [hLEq]
            simp
      _ = (2 : ℤ) ^ (L - 1) * 2 := by
            rw [pow_succ]
  rw [hPowL] at hEq
  linear_combination hEq

end Mersenne
end Collatz3
