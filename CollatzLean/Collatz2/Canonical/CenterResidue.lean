import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Orbit.RealizationRecovery
import CollatzLean.Collatz2.Orbit.RunDefect
import CollatzLean.Collatz2.Geometry.Center

/-!
# Collatz2 Canonical: 同一 center の local residue shadows

valid nonempty genuine word では canonical start/end から normalized `Runs` を回復できる。
両 boundary が odd なので、同じ displacement root が二つの local modulus に現れる。

* start 側: `Δ(start)` は `2*A` の倍数
* endpoint 側: `Δ(end)` は `2*C` の倍数

canonical start/end を同一 rational center の二つの division-free residue shadow として読む。
-/

namespace Collatz2
namespace Word

/-- Canonical realization recovers a normalized run for a valid word. -/
theorem canonicalRuns
    {w : Word}
    (hvalid : w.Valid) :
    Runs w (canonicalStart w) (canonicalEnd w) :=
  (canonicalEnd_realizes w).toRuns_of_valid_of_end_odd
    hvalid (canonicalEnd_odd w)

/-- Canonical start is odd for a valid nonempty word. -/
theorem canonicalStart_odd_of_valid_nonempty
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    Odd (canonicalStart w) :=
  (canonicalRuns hvalid).start_odd_of_ne_nil hne

/--
Every nonempty normalized run sees the displacement root modulo `2*A` at its
start: start defect is an integer multiple of `2*twoCoeff`.
-/
theorem Runs.startDefect_eq_two_mul_twoCoeff_mul
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    ∃ k : ℤ,
      Word.startDefect w x =
        (2 * ((AffineTransfer.ofWord w).twoCoeff : ℤ)) * k := by
  have hx := h.start_odd_of_ne_nil hne
  have hy := h.end_odd_of_ne_nil hne
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨(b : ℤ) - (a : ℤ), ?_⟩
  rw [h.startDefect_eq_displacement]
  rw [ha, hb]
  push_cast
  ring

/-- High-level root-mod form of the start-side theorem. -/
theorem Runs.start_isRootMod_twoCoeff
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    (AffineTransfer.ofWord w).displacementForm.IsRootMod
      (2 * (AffineTransfer.ofWord w).twoCoeff) (x : ℤ) := by
  rcases startDefect_eq_two_mul_twoCoeff_mul h hne with ⟨k, hk⟩
  exact ⟨k, by simpa [Word.startDefect, AffineTransfer.startDefect] using hk⟩

/-- Canonical start is the `2*A` local shadow of the displacement root. -/
theorem canonicalStart_centerRoot_mod_twoCoeff
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    ∃ k : ℤ,
      Word.startDefect w (canonicalStart w) =
        (2 * ((AffineTransfer.ofWord w).twoCoeff : ℤ)) * k :=
  Runs.startDefect_eq_two_mul_twoCoeff_mul (canonicalRuns hvalid) hne

/-- Canonical start expressed directly as a root-mod statement. -/
theorem canonicalStart_isRootMod_twoCoeff
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    (AffineTransfer.ofWord w).displacementForm.IsRootMod
      (2 * (AffineTransfer.ofWord w).twoCoeff) (canonicalStart w : ℤ) :=
  Runs.start_isRootMod_twoCoeff (canonicalRuns hvalid) hne

/--
Every nonempty normalized run sees the same displacement root modulo `2*C` at
its endpoint.
-/
theorem Runs.endDisplacement_eq_two_mul_oddCoeff_mul
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    ∃ k : ℤ,
      (AffineTransfer.ofWord w).displacementForm.eval (y : ℤ) =
        (2 * ((AffineTransfer.ofWord w).oddCoeff : ℤ)) * k := by
  have hx := h.start_odd_of_ne_nil hne
  have hy := h.end_odd_of_ne_nil hne
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨(b : ℤ) - (a : ℤ), ?_⟩
  have hreal : (AffineTransfer.ofWord w).Realizes x y := h.realizes
  rw [hreal.displacementForm_eval_end]
  rw [ha, hb]
  push_cast
  ring

/-- High-level root-mod form of the endpoint-side theorem. -/
theorem Runs.end_isRootMod_oddCoeff
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    (AffineTransfer.ofWord w).displacementForm.IsRootMod
      (2 * (AffineTransfer.ofWord w).oddCoeff) (y : ℤ) := by
  rcases endDisplacement_eq_two_mul_oddCoeff_mul h hne with ⟨k, hk⟩
  exact ⟨k, hk⟩

/-- Canonical endpoint is the `2*C` local shadow of the same displacement root. -/
theorem canonicalEnd_centerRoot_mod_oddCoeff
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    ∃ k : ℤ,
      (AffineTransfer.ofWord w).displacementForm.eval (canonicalEnd w : ℤ) =
        (2 * ((AffineTransfer.ofWord w).oddCoeff : ℤ)) * k :=
  Runs.endDisplacement_eq_two_mul_oddCoeff_mul (canonicalRuns hvalid) hne

/-- Canonical endpoint expressed directly as a root-mod statement. -/
theorem canonicalEnd_isRootMod_oddCoeff
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    (AffineTransfer.ofWord w).displacementForm.IsRootMod
      (2 * (AffineTransfer.ofWord w).oddCoeff) (canonicalEnd w : ℤ) :=
  Runs.end_isRootMod_oddCoeff (canonicalRuns hvalid) hne

end Word
end Collatz2
