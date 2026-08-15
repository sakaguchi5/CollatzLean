import CollatzLean.Collatz3.Geometry.CriticalProfile

/-!
# Collatz3: integer Ferrers deficit

modular Ferrers shadowへ落とす前に、first-crossing critical roof から actual word が
失った affine translation を正の自然数として保持する。

各 prefix cut `k` について

  critical contribution - actual contribution

を取り、その総和を `integerFerrersDeficit` とする。

FirstCrossing では各差が genuine natural deficit であり、exact に

  Bcrit = IntegerFerrersDeficit + B

を得る。
-/

namespace Collatz3

open Collatz2

namespace Word

/-- 一つの prefix column が critical roof から失った整数 affine weight。 -/
def integerFerrersDeficitTerm
    (w : Collatz2.Word)
    (k : ℕ) : ℕ :=
  criticalAffineTerm (Collatz2.Word.oddSteps w) k -
    affinePathTerm w k

/-- 全 prefix column の positive integer deficit。 -/
def integerFerrersDeficit
    (w : Collatz2.Word) : ℕ :=
  Finset.sum (Finset.range (Collatz2.Word.oddSteps w))
    (fun k => integerFerrersDeficitTerm w k)

/--
FirstCrossing では critical budget が actual affine translation と integer deficit に
exact に分解される。
-/
theorem criticalAffineConst_eq_integerFerrersDeficit_add_affineConst
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w) :
    criticalAffineConst (Collatz2.Word.oddSteps w) =
      integerFerrersDeficit w + Collatz2.Word.affineConst w := by
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
    (w : Collatz2.Word) :
    0 ≤ integerFerrersDeficit w :=
  Nat.zero_le _

/-- deficit zero なら critical budget と actual translation は一致する。 -/
theorem affineConst_eq_criticalAffineConst_of_deficit_eq_zero
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w)
    (hZero : integerFerrersDeficit w = 0) :
    Collatz2.Word.affineConst w =
      criticalAffineConst (Collatz2.Word.oddSteps w) := by
  have hEq := criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hF
  rw [hZero, zero_add] at hEq
  exact hEq.symm

end Word
end Collatz3
