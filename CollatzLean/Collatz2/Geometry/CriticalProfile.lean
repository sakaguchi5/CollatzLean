import CollatzLean.Collatz2.Geometry.RankStrip
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz2 Geometry: critical first-crossing profile

FirstCrossing proper prefix が coefficient-expanding でいられる最大 2-depth
`criticalHeight(k)` を roof として使う。

actual prefix depth

  h_k = prefixTwoDepth w k

との差

  criticalDefect(k) = criticalHeight(k) - h_k

を一般 word geometry として保持する。
-/

namespace Collatz2
namespace Word

/-- critical roof から actual prefix が何段下にいるか。 -/
def criticalDefect
    (w : Word)
    (k : ℕ) : ℕ :=
  criticalHeight k - prefixTwoDepth w k

/-- 既存 `extraDepth` は同じ critical defect。 -/
theorem criticalDefect_eq_extraDepth
    (w : Word)
    (k : ℕ) :
    criticalDefect w k = extraDepth w k := by
  rfl

/-- affine translation の `k` 番目の actual contribution。 -/
def affinePathTerm
    (w : Word)
    (k : ℕ) : ℕ :=
  2 ^ prefixTwoDepth w k *
    3 ^ (oddSteps w - (k + 1))

@[simp] theorem affinePathTerm_cons_zero
    (e : ℕ)
    (w : Word) :
    affinePathTerm (e :: w) 0 = 3 ^ oddSteps w := by
  simp [affinePathTerm, prefixTwoDepth]

/-- cons word の positive-index contribution は tail contribution の `2^e` 倍。 -/
theorem affinePathTerm_cons_succ
    (e : ℕ)
    (w : Word)
    (k : ℕ) :
    affinePathTerm (e :: w) (k + 1) =
      2 ^ e * affinePathTerm w k := by
  have hSub :
      oddSteps (e :: w) - ((k + 1) + 1) =
        oddSteps w - (k + 1) := by
    simp only [oddSteps_cons]
    omega
  unfold affinePathTerm prefixTwoDepth
  rw [hSub]
  simp only [List.take_succ_cons, twoSteps_cons]
  rw [pow_add]
  ring

/-- actual affine translation の indexed sum。 -/
def affinePathSum
    (w : Word) : ℕ :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k => affinePathTerm w k)

/-- indexed prefix contribution の総和は exact に `affineConst`。 -/
theorem affinePathSum_eq_affineConst
    (w : Word) :
    affinePathSum w = affineConst w := by
  induction w with
  | nil =>
      simp [affinePathSum, affinePathTerm, oddSteps, affineConst]
  | cons e w ih =>
      unfold affinePathSum
      rw [oddSteps_cons, Finset.sum_range_succ']
      rw [affinePathTerm_cons_zero]
      simp_rw [affinePathTerm_cons_succ]
      rw [← Finset.mul_sum]
      change
        2 ^ e * affinePathSum w + 3 ^ oddSteps w = affineConst (e :: w)
      rw [ih, affineConst_cons]
      ac_rfl

/-- odd-step 数 `p` の critical roof contribution。 -/
def criticalAffineTerm
    (p k : ℕ) : ℕ :=
  2 ^ criticalHeight k * 3 ^ (p - (k + 1))

/-- word 内部配置に依存しない critical-roof affine budget。 -/
def criticalAffineConst
    (p : ℕ) : ℕ :=
  Finset.sum (Finset.range p) (fun k => criticalAffineTerm p k)

/-- FirstCrossing では各 actual contribution は critical roof contribution 以下。 -/
theorem affinePathTerm_le_criticalAffineTerm_of_firstCrossing
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    affinePathTerm w k ≤ criticalAffineTerm (oddSteps w) k := by
  have hDepth : prefixTwoDepth w k ≤ criticalHeight k := by
    by_cases hk0 : k = 0
    · subst k
      simp [prefixTwoDepth]
    · exact hF.prefixTwoDepth_le_criticalHeight
        (Nat.pos_of_ne_zero hk0) hkLt
  have hPow :
      2 ^ prefixTwoDepth w k ≤ 2 ^ criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
  unfold affinePathTerm criticalAffineTerm
  exact Nat.mul_le_mul_right _ hPow

/-- FirstCrossing actual translation は critical roof budget 以下。 -/
theorem affineConst_le_criticalAffineConst_of_firstCrossing
    {w : Word}
    (hF : FirstCrossing w) :
    affineConst w ≤ criticalAffineConst (oddSteps w) := by
  rw [← affinePathSum_eq_affineConst]
  unfold affinePathSum criticalAffineConst
  apply Finset.sum_le_sum
  intro k hk
  exact affinePathTerm_le_criticalAffineTerm_of_firstCrossing hF
    (Finset.mem_range.mp hk)

end Word
end Collatz2
