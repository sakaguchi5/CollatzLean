import CollatzLean.Collatz3.Bridge.MersenneRuns
import CollatzLean.Collatz3.Bridge.RunsToCanonical


/-!
# Collatz3 Bridge: Mersenne block と canonical run arithmetic

Mersenne `BlockData` から得られる actual `Runs` を、既存 canonical lift classification へ直結する。
新しい canonical object は導入しない。
-/

namespace Collatz3
namespace Bridge

private theorem blockWord_nonempty
    {d r : ℕ}
    (hd : 0 < d) :
    Mersenne.blockWord d r ≠ [] := by
  intro hNil
  have hSteps := Mersenne.blockWord_oddSteps (r := r) hd
  rw [hNil] at hSteps
  simp [Word.oddSteps] at hSteps
  omega

/-- Mersenne block source は対応 exponent word の canonical residue class に属する。 -/
theorem mersenneBlockData_start_mod_eq_canonicalStart
    {d r u x y : ℕ}
    (h : Mersenne.BlockData d r u x y) :
    x % Word.oddEndpointModulus (Mersenne.blockWord d r) =
      Word.canonicalStart (Mersenne.blockWord d r) := by
  have hRun := mersenneBlockData_runs h
  exact hRun.start_mod_eq_canonicalStart (blockWord_nonempty h.depth_pos)

/-- Mersenne block realization は canonical pair の affine lift として一意に表示できる。 -/
theorem mersenneBlockData_exists_canonicalLift
    {d r u x y : ℕ}
    (h : Mersenne.BlockData d r u x y) :
    ∃ k : ℕ,
      x = Word.canonicalStart (Mersenne.blockWord d r) +
          Word.oddEndpointModulus (Mersenne.blockWord d r) * k ∧
      y = Word.canonicalEnd (Mersenne.blockWord d r) +
          2 * (3 ^ Word.oddSteps (Mersenne.blockWord d r)) * k := by
  have hRun := mersenneBlockData_runs h
  exact hRun.exists_canonicalLift (blockWord_nonempty h.depth_pos)

/-- canonical start は任意の同型 Mersenne block source 以下。 -/
theorem mersenneBlockData_canonicalStart_le_start
    {d r u x y : ℕ}
    (h : Mersenne.BlockData d r u x y) :
    Word.canonicalStart (Mersenne.blockWord d r) ≤ x := by
  have hRun := mersenneBlockData_runs h
  exact hRun.canonicalStart_le_start (blockWord_nonempty h.depth_pos)

end Bridge
end Collatz3
