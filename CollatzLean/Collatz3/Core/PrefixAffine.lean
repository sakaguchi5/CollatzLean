import CollatzLean.Collatz3.Core.PrefixDepth
import CollatzLean.Collatz3.Core.WordTransfer

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Collatz3: affine translation as a prefix-depth sum

word の affine translation `B` を、各 odd cut の prefix two-depth から作る
有限和として再表現する。これは新しい正本ではなく `affineConst` の derived view。
-/

namespace Collatz3
namespace Word

open scoped BigOperators

/-- word の cut `k` が affine translation に与える monomial。 -/
def affinePrefixTerm
    (w : Word)
    (k : ℕ) : ℕ :=
  2 ^ prefixTwoDepth w k *
    3 ^ (oddSteps w - (k + 1))

/-- prefix-depth 表現による affine numerator。 -/
def affinePrefixNumerator
    (w : Word) : ℕ :=
  ∑ k ∈ Finset.range (oddSteps w), affinePrefixTerm w k

@[simp] theorem affinePrefixNumerator_nil :
    affinePrefixNumerator ([] : Word) = 0 := by
  simp [affinePrefixNumerator]

/-- head exponent を一つ追加したときの prefix numerator recurrence。 -/
theorem affinePrefixNumerator_cons
    (e : ℕ)
    (tail : Word) :
    affinePrefixNumerator (e :: tail) =
      3 ^ oddSteps tail +
        2 ^ e * affinePrefixNumerator tail := by
  unfold affinePrefixNumerator
  rw [oddSteps_cons]
  rw [Finset.sum_range_succ']
  have hShift :
      (∑ k ∈ Finset.range (oddSteps tail),
        affinePrefixTerm (e :: tail) (k + 1)) =
      2 ^ e *
        (∑ k ∈ Finset.range (oddSteps tail),
          affinePrefixTerm tail k) := by
    calc
      (∑ k ∈ Finset.range (oddSteps tail),
          affinePrefixTerm (e :: tail) (k + 1))
          =
          ∑ k ∈ Finset.range (oddSteps tail),
            2 ^ e * affinePrefixTerm tail k := by
              apply Finset.sum_congr rfl
              intro k hk
              have hkLt : k < oddSteps tail :=
                Finset.mem_range.mp hk
              have hSub :
                  oddSteps tail + 1 - ((k + 1) + 1) =
                    oddSteps tail - (k + 1) := by
                omega
              unfold affinePrefixTerm
              rw [oddSteps_cons, prefixTwoDepth_cons_succ, hSub, pow_add]
              ring
      _ =
          2 ^ e *
            (∑ k ∈ Finset.range (oddSteps tail),
              affinePrefixTerm tail k) := by
                rw [← Finset.mul_sum]
  rw [hShift]
  have hZero :
      affinePrefixTerm (e :: tail) 0 =
        3 ^ oddSteps tail := by
    unfold affinePrefixTerm
    simp [prefixTwoDepth, oddSteps]
  rw [hZero]
  exact Nat.add_comm _ _

/-- prefix-depth finite sum は既存の唯一の translation `affineConst` と一致。 -/
theorem affinePrefixNumerator_eq_affineConst
    (w : Word) :
    affinePrefixNumerator w = affineConst w := by
  induction w with
  | nil =>
      simp
  | cons e tail ih =>
      rw [affinePrefixNumerator_cons]
      rw [affineConst_cons]
      rw [ih]

end Word
end Collatz3
