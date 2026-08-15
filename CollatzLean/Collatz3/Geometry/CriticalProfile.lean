import CollatzLean.Collatz2.Geometry.CriticalProfile

/-!
# Collatz3 compatibility wrapper

critical profile の正本は `Collatz2.Geometry.CriticalProfile` へ移動した。
もし既存 import を移行できたらこの wrapper は削除可能。
-/

namespace Collatz3
namespace Word

abbrev criticalDefect
    (w : Collatz2.Word) (k : ℕ) : ℕ :=
  Collatz2.Word.criticalDefect w k

abbrev affinePathTerm
    (w : Collatz2.Word) (k : ℕ) : ℕ :=
  Collatz2.Word.affinePathTerm w k

abbrev affinePathSum
    (w : Collatz2.Word) : ℕ :=
  Collatz2.Word.affinePathSum w

abbrev criticalAffineTerm
    (p k : ℕ) : ℕ :=
  Collatz2.Word.criticalAffineTerm p k

abbrev criticalAffineConst
    (p : ℕ) : ℕ :=
  Collatz2.Word.criticalAffineConst p

theorem criticalDefect_eq_extraDepth
    (w : Collatz2.Word)
    (k : ℕ) :
    criticalDefect w k = Collatz2.Word.extraDepth w k :=
  Collatz2.Word.criticalDefect_eq_extraDepth w k

@[simp] theorem affinePathTerm_cons_zero
    (e : ℕ)
    (w : Collatz2.Word) :
    affinePathTerm (e :: w) 0 = 3 ^ Collatz2.Word.oddSteps w :=
  Collatz2.Word.affinePathTerm_cons_zero e w

theorem affinePathTerm_cons_succ
    (e : ℕ)
    (w : Collatz2.Word)
    (k : ℕ) :
    affinePathTerm (e :: w) (k + 1) =
      2 ^ e * affinePathTerm w k :=
  Collatz2.Word.affinePathTerm_cons_succ e w k

theorem affinePathSum_eq_affineConst
    (w : Collatz2.Word) :
    affinePathSum w = Collatz2.Word.affineConst w :=
  Collatz2.Word.affinePathSum_eq_affineConst w

theorem affinePathTerm_le_criticalAffineTerm_of_firstCrossing
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w)
    {k : ℕ}
    (hkLt : k < Collatz2.Word.oddSteps w) :
    affinePathTerm w k ≤ criticalAffineTerm (Collatz2.Word.oddSteps w) k :=
  Collatz2.Word.affinePathTerm_le_criticalAffineTerm_of_firstCrossing hF hkLt

theorem affineConst_le_criticalAffineConst_of_firstCrossing
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w) :
    Collatz2.Word.affineConst w ≤ criticalAffineConst (Collatz2.Word.oddSteps w) :=
  Collatz2.Word.affineConst_le_criticalAffineConst_of_firstCrossing hF

end Word
end Collatz3
