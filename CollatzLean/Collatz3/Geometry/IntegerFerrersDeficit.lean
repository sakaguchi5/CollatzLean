import CollatzLean.Collatz2.Geometry.IntegerFerrersDeficit
import CollatzLean.Collatz3.Geometry.CriticalProfile

/-!
# Collatz3 compatibility wrapper

integer Ferrers deficit の正本は `Collatz2.Geometry.IntegerFerrersDeficit` へ移動した。
既存 import を移行できたらこの wrapper は削除可能。
-/

namespace Collatz3
namespace Word

abbrev integerFerrersDeficitTerm
    (w : Collatz2.Word) (k : ℕ) : ℕ :=
  Collatz2.Word.integerFerrersDeficitTerm w k

abbrev integerFerrersDeficit
    (w : Collatz2.Word) : ℕ :=
  Collatz2.Word.integerFerrersDeficit w

theorem criticalAffineConst_eq_integerFerrersDeficit_add_affineConst
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w) :
    criticalAffineConst (Collatz2.Word.oddSteps w) =
      integerFerrersDeficit w + Collatz2.Word.affineConst w :=
  Collatz2.Word.criticalAffineConst_eq_integerFerrersDeficit_add_affineConst hF

theorem integerFerrersDeficit_nonneg
    (w : Collatz2.Word) :
    0 ≤ integerFerrersDeficit w :=
  Collatz2.Word.integerFerrersDeficit_nonneg w

theorem affineConst_eq_criticalAffineConst_of_deficit_eq_zero
    {w : Collatz2.Word}
    (hF : Collatz2.Word.FirstCrossing w)
    (hZero : integerFerrersDeficit w = 0) :
    Collatz2.Word.affineConst w =
      criticalAffineConst (Collatz2.Word.oddSteps w) :=
  Collatz2.Word.affineConst_eq_criticalAffineConst_of_deficit_eq_zero hF hZero

end Word
end Collatz3
