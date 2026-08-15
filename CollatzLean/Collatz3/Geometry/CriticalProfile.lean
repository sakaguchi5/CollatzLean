import CollatzLean.Collatz2.Geometry.RankStrip
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz3: critical first-crossing profile

FirstCrossing proper prefix が coefficient-expanding でいられる最大 2-depth
`criticalHeight(k)` を roof として使う。

actual prefix depth

  h_k = prefixTwoDepth w k

との差

  criticalDefect(k) = criticalHeight(k) - h_k

を、rank quotient より先に意味のある幾何量として保持する。

さらに affine translation を prefix index で直接評価できる形にする。
-/

namespace Collatz3

open Collatz2

namespace Word

/-- critical roof から actual prefix が何段下にいるか。 -/
def criticalDefect
    (w : Collatz2.Word)
    (k : ℕ) : ℕ :=
  Collatz2.Word.criticalHeight k -
    Collatz2.Word.prefixTwoDepth w k

/-- Collatz2 の `extraDepth` は同じ critical defect。 -/
theorem criticalDefect_eq_extraDepth
    (w : Collatz2.Word)
    (k : ℕ) :
    criticalDefect w k = Collatz2.Word.extraDepth w k := by
  rfl

/-- affine translation の `k` 番目の actual contribution。 -/
def affinePathTerm
    (w : Collatz2.Word)
    (k : ℕ) : ℕ :=
  2 ^ Collatz2.Word.prefixTwoDepth w k *
    3 ^ (Collatz2.Word.oddSteps w - (k + 1))

@[simp] theorem affinePathTerm_cons_zero
    (e : ℕ)
    (w : Collatz2.Word) :
    affinePathTerm (e :: w) 0 =
      3 ^ Collatz2.Word.oddSteps w := by
  simp [affinePathTerm, Collatz2.Word.prefixTwoDepth]

/-- cons word の positive-index contribution は tail contribution の `2^e` 倍。 -/
theorem affinePathTerm_cons_succ
    (e : ℕ)
    (w : Collatz2.Word)
    (k : ℕ) :
    affinePathTerm (e :: w) (k + 1) =
      2 ^ e * affinePathTerm w k := by
  have hSub :
      Collatz2.Word.oddSteps (e :: w) - ((k + 1) + 1) =
        Collatz2.Word.oddSteps w - (k + 1) := by
    simp only [Collatz2.Word.oddSteps_cons]
    omega
  unfold affinePathTerm Collatz2.Word.prefixTwoDepth
  rw [hSub]
  simp only [List.take_succ_cons, Collatz2.Word.twoSteps_cons]
  rw [pow_add]
  ring

/-- actual affine translation の indexed sum。 -/
def affinePathSum
    (w : Collatz2.Word) : ℕ :=
  Finset.sum (Finset.range (Collatz2.Word.oddSteps w))
    (fun k => affinePathTerm w k)

/-- indexed prefix contribution の総和は exact に `affineConst`。 -/
theorem affinePathSum_eq_affineConst
    (w : Collatz2.Word) :
    affinePathSum w = Collatz2.Word.affineConst w := by
  induction w with
  | nil =>
      simp [affinePathSum, affinePathTerm,
        Collatz2.Word.oddSteps, Collatz2.Word.affineConst]
  | cons e w ih =>
      unfold affinePathSum
      rw [Collatz2.Word.oddSteps_cons, Finset.sum_range_succ']
      rw [affinePathTerm_cons_zero]
      simp_rw [affinePathTerm_cons_succ]
      rw [← Finset.mul_sum]
      change
        2 ^ e * affinePathSum w +
            3 ^ Collatz2.Word.oddSteps w =
          Collatz2.Word.affineConst (e :: w)
      rw [ih, Collatz2.Word.affineConst_cons]
      ac_rfl

/-- odd-step 数 `p` の critical roof contribution。 -/
def criticalAffineTerm
    (p k : ℕ) : ℕ :=
  2 ^ Collatz2.Word.criticalHeight k *
    3 ^ (p - (k + 1))

/--
first-crossing class で使える critical-roof affine budget。
word の内部配置には依存せず odd-step 数 `p` だけで決まる。
-/
def criticalAffineConst
    (p : ℕ) : ℕ :=
  Finset.sum (Finset.range p)
    (fun k => criticalAffineTerm p k)

/-- FirstCrossing では各 actual contribution は critical roof contribution 以下。 -/
theorem affinePathTerm_le_criticalAffineTerm_of_firstCrossing
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w)
    {k : ℕ}
    (hkLt : k < Collatz2.Word.oddSteps w) :
    affinePathTerm w k ≤
      criticalAffineTerm (Collatz2.Word.oddSteps w) k := by
  have hDepth :
      Collatz2.Word.prefixTwoDepth w k ≤
        Collatz2.Word.criticalHeight k := by
    by_cases hk0 : k = 0
    · subst k
      simp [Collatz2.Word.prefixTwoDepth]
    · exact hF.prefixTwoDepth_le_criticalHeight
        (Nat.pos_of_ne_zero hk0) hkLt
  have hPow :
      2 ^ Collatz2.Word.prefixTwoDepth w k ≤
        2 ^ Collatz2.Word.criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
  unfold affinePathTerm criticalAffineTerm
  exact Nat.mul_le_mul_right _ hPow

/-- FirstCrossing actual translation は critical roof budget 以下。 -/
theorem affineConst_le_criticalAffineConst_of_firstCrossing
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w) :
    Collatz2.Word.affineConst w ≤
      criticalAffineConst (Collatz2.Word.oddSteps w) := by
  rw [← affinePathSum_eq_affineConst]
  unfold affinePathSum criticalAffineConst
  apply Finset.sum_le_sum
  intro k hk
  exact affinePathTerm_le_criticalAffineTerm_of_firstCrossing hF
    (Finset.mem_range.mp hk)

end Word
end Collatz3
