import CollatzLean.Collatz2.RecordFerrers.Factorization.BlockFerrersDeficit

/-!
# Record–Ferrers Phase A: Ferrers reconstruction

Phase A の exact fixed-chord equivalence を reconstruction API としてまとめる。
full Ferrers shape / full height profile から valid word へ lossless に戻す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- bounded Ferrers shape から fixed-chord point を復元する canonical decoder。 -/
def reconstruct
    {p H : ℕ}
    (S : FiberShape p H) : FiberPoint p H :=
  S.toFiberPoint

/-- reconstruction 後の Ferrers shape は元に戻る。 -/
theorem reconstruct_shape
    {p H : ℕ}
    (S : FiberShape p H) :
    (reconstruct S).toFerrersShape = S.shape :=
  S.toFerrersShape_toFiberPoint

/-- positive fixed-chord point を encode して decode すると元に戻る。 -/
theorem reconstruct_encode
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p) :
    reconstruct (x.toFiberShape hp) = x :=
  x.toFiberPoint_toFiberShape hp

/-- full Ferrers shape は positive fixed-chord word の complete invariant。 -/
theorem fiberPoint_eq_of_same_shape
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hShape : x.toFerrersShape = y.toFerrersShape) :
    x = y :=
  FiberPoint.toFerrersShape_injective hShape

/-- full Ferrers shape equality から underlying exponent word equality。 -/
theorem word_eq_of_same_shape
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hShape : x.toFerrersShape = y.toFerrersShape) :
    x.word = y.word := by
  have hxy := fiberPoint_eq_of_same_shape hShape
  exact congrArg (fun z => z.word) hxy

/-- displacement bridge が proper cuts 全てで 0 なら fixed-chord points は同一。 -/
theorem fiberPoint_eq_of_displacement_zero
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hZero :
      ∀ k : ℕ,
        k < p →
        profileDisplacement x y k = 0) :
    x = y := by
  apply FiberPoint.ext
  intro k hk
  have h := hZero k hk
  unfold profileDisplacement at h
  have hCast : (y.height k : ℤ) = (x.height k : ℤ) := by
    linarith
  exact_mod_cast hCast.symm

/-- fixed `(p,H)` と affineConst は valid word を復元する。 -/
theorem fiberPoint_eq_of_same_affineConst
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hB : affineConst x.word = affineConst y.word) :
    x = y := by
  have hpEq : oddSteps x.word = oddSteps y.word := by
    calc
      oddSteps x.word = p := x.oddSteps_eq
      _ = oddSteps y.word := y.oddSteps_eq.symm
  have hHEq : twoSteps x.word = twoSteps y.word := by
    calc
      twoSteps x.word = H := x.twoSteps_eq
      _ = twoSteps y.word := y.twoSteps_eq.symm
  have hw :=
    valid_word_unique_of_oddSteps_twoSteps_affineConst
      x.valid y.valid hpEq hHEq hB
  cases x with
  | mk xw xv xp xH =>
      cases y with
      | mk yw yv yp yH =>
          dsimp at hw
          subst yw
          rfl

/-- reconstructed word の affine translation は shape weighted area から exact に読める。 -/
theorem reconstruct_affineConst
    {p H : ℕ}
    (S : FiberShape p H) :
    affineConst (reconstruct S).word =
      baseAffineConst p + weightedArea S.shape := by
  exact affineConst_toFiberPoint_eq_base_add_weightedArea S

end RecordFerrers
end Collatz2
