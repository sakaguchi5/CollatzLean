import CollatzLean.Collatz2.Geometry.CriticalProfile

/-!
# Collatz2 Geometry: integer Ferrers deficit

modular Ferrers shadowへ落とす前に、first-crossing critical roof から actual word が
失った affine translation を正の自然数として保持する。
-/

namespace Collatz2
namespace Word

/-- 一つの prefix column が critical roof から失った整数 affine weight。 -/
def integerFerrersDeficitTerm
    (w : Word)
    (k : ℕ) : ℕ :=
  criticalAffineTerm (oddSteps w) k - affinePathTerm w k

/-- 全 prefix column の positive integer deficit。 -/
def integerFerrersDeficit
    (w : Word) : ℕ :=
  Finset.sum (Finset.range (oddSteps w))
    (fun k => integerFerrersDeficitTerm w k)

/--
FirstCrossing では critical budget が actual affine translation と integer deficit に
exact に分解される。
-/
theorem criticalAffineConst_eq_integerFerrersDeficit_add_affineConst
    {w : Word}
    (hF : FirstCrossing w) :
    criticalAffineConst (oddSteps w) =
      integerFerrersDeficit w + affineConst w := by
  rw [← affinePathSum_eq_affineConst]
  unfold criticalAffineConst integerFerrersDeficit affinePathSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hle := affinePathTerm_le_criticalAffineTerm_of_firstCrossing hF
    (Finset.mem_range.mp hk)
  unfold integerFerrersDeficitTerm
  exact (Nat.sub_add_cancel hle).symm

/-- deficit は定義上 nonnegative。 -/
theorem integerFerrersDeficit_nonneg
    (w : Word) :
    0 ≤ integerFerrersDeficit w :=
  Nat.zero_le _

/-- deficit zero なら critical budget と actual translation は一致する。 -/
theorem affineConst_eq_criticalAffineConst_of_deficit_eq_zero
    {w : Word}
    (hF : FirstCrossing w)
    (hZero : integerFerrersDeficit w = 0) :
    affineConst w = criticalAffineConst (oddSteps w) := by
  have hEq := criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hF
  rw [hZero, zero_add] at hEq
  exact hEq.symm

end Word
end Collatz2
