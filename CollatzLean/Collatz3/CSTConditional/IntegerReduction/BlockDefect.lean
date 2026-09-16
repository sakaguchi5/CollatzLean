import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleBlockClassification
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


/-!
# Collatz3 CSTConditional IntegerReduction: block 境界 defect

block length 列 `r_n` だけから

* 境界 index `F_n = Σ r_i`
* 境界 total depth `D_n = Σ beattyIndex(r_i)`
* defect `δ_n = beattyIndex(F_n) - D_n`

を作る。

ここでは A/C symbol を primitive にしない。
defect increment が `0/1` であることは Beatty carry から derived theorem として得る。
-/

namespace Collatz3
namespace IntegerReduction

open scoped BigOperators
open Critical

/-- 最初の `n` block の長さ和。 -/
def boundaryIndex
    (r : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, r i

/-- 最初の `n` block の Beatty depth 和。 -/
def boundaryDepth
    (r : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, Critical.beattyIndex (r i)

/-- block 境界 defect。 -/
def boundaryDefect
    (r : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  Critical.beattyIndex (boundaryIndex r n) - boundaryDepth r n

@[simp] theorem boundaryIndex_zero
    (r : ℕ → ℕ) :
    boundaryIndex r 0 = 0 := by
  simp [boundaryIndex]

@[simp] theorem boundaryDepth_zero
    (r : ℕ → ℕ) :
    boundaryDepth r 0 = 0 := by
  simp [boundaryDepth]

@[simp] theorem boundaryDefect_zero
    (r : ℕ → ℕ) :
    boundaryDefect r 0 = 0 := by
  simp [boundaryDefect]

/-- 境界 index の一段 recurrence。 -/
theorem boundaryIndex_succ
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryIndex r (n + 1) = boundaryIndex r n + r n := by
  simp [boundaryIndex, Finset.sum_range_succ]

/-- 境界 depth の一段 recurrence。 -/
theorem boundaryDepth_succ
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDepth r (n + 1) =
      boundaryDepth r n + Critical.beattyIndex (r n) := by
  simp [boundaryDepth, Finset.sum_range_succ]

/--
Beatty superadditivity により、境界 depth 和は absolute Beatty roof 以下。
従って `boundaryDefect` の自然数減算は情報を失わない。
-/
theorem boundaryDepth_le_beattyIndex_boundaryIndex
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDepth r n ≤ Critical.beattyIndex (boundaryIndex r n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hAdd :=
        Critical.beattyIndex_add_lower (boundaryIndex r n) (r n)
      rw [boundaryIndex_succ, boundaryDepth_succ]
      omega

/--
一 block 進んだ defect 増分は absolute position と block length の Beatty carry そのもの。
-/
theorem boundaryDefect_succ_eq_add_carry
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDefect r (n + 1) =
      boundaryDefect r n +
        Critical.beattyCarry (boundaryIndex r n) (r n) := by
  have hDepth := boundaryDepth_le_beattyIndex_boundaryIndex r n
  have hAdd :=
    Critical.beattyIndex_add_eq (boundaryIndex r n) (r n)
  unfold boundaryDefect
  rw [boundaryIndex_succ, boundaryDepth_succ, hAdd]
  omega

/-- defect は一 block ごとに据え置きか `+1`。 -/
theorem boundaryDefect_succ_eq_or_succ
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDefect r (n + 1) = boundaryDefect r n ∨
      boundaryDefect r (n + 1) = boundaryDefect r n + 1 := by
  have hStep := boundaryDefect_succ_eq_add_carry r n
  rcases Critical.beattyCarry_eq_zero_or_one (boundaryIndex r n) (r n) with h0 | h1
  · left
    rw [hStep, h0]
    omega
  · right
    rw [hStep, h1]

/--
境界 defect は各 block carry の有限和。
A/C count を primitive にせず、必要なときにこの式から読む。
-/
theorem boundaryDefect_eq_sum_carry
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDefect r n =
      ∑ i ∈ Finset.range n,
        Critical.beattyCarry (boundaryIndex r i) (r i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [boundaryDefect_succ_eq_add_carry, ih]
      simp [Finset.sum_range_succ, Nat.add_comm]

/-- defect は block 数以下。 -/
theorem boundaryDefect_le_blockCount
    (r : ℕ → ℕ)
    (n : ℕ) :
    boundaryDefect r n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hStep := boundaryDefect_succ_eq_or_succ r n
      rcases hStep with hFlat | hRise
      · rw [hFlat]
        omega
      · rw [hRise]
        omega

end IntegerReduction
end Collatz3
