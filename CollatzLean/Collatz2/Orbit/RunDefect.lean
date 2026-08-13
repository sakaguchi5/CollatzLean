import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Local.Defect

/-!
# Collatz2 Orbit: run-level defect corollary

`Local.Defect` は `AffineTransfer.Realizes` / `Word.Realizes` までに依存を留める。
stepwise trajectory `Runs` に固有の corollary だけを Orbit 層で導く。

これにより依存方向を

  Local.Defect -> Orbit.Runs

ではなく

  Local.Defect + Orbit.Runs -> Orbit.RunDefect

へ戻す。
-/

namespace Collatz2
namespace Runs

/-- Stepwise run start evaluation is exact actual displacement. -/
theorem startDefect_eq_displacement
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.startDefect w x =
      ((AffineTransfer.ofWord w).twoCoeff : ℤ) *
        ((y : ℤ) - (x : ℤ)) := by
  have hT : (AffineTransfer.ofWord w).Realizes x y := h.realizes
  exact hT.startDefect_eq_displacement

end Runs
end Collatz2
