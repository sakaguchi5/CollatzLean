import CollatzLean.Collatz2.Core.DisplacementForm
import CollatzLean.Collatz2.Local.DeterminantSign
import Mathlib.Tactic.Linarith

/-!
# Collatz2: displacement-form evaluation と defect

defect は新しい trajectory data ではなく `DisplacementForm` の評価値である。
realization `x -> y` 上では

  `Δ_T(x) = A * (y-x)`
  `Δ_T(y) = C * (y-x)`

となり、positive return / descent は評価値の符号の corollary になる。
-/

namespace Collatz2

namespace AffineTransfer

/-- Start defect is displacement-form evaluation at `x`. -/
def startDefect (T : AffineTransfer) (x : ℕ) : ℤ :=
  T.displacementForm.eval (x : ℤ)

/-- Endpoint defect keeps the historical reverse-displacement sign. -/
def endpointDefect (T : AffineTransfer) (y : ℕ) : ℤ :=
  -T.displacementForm.eval (y : ℤ)

@[simp] theorem startDefect_eq_displacementForm_eval
    (T : AffineTransfer) (x : ℕ) :
    T.startDefect x = T.displacementForm.eval (x : ℤ) := rfl

@[simp] theorem endpointDefect_eq_neg_displacementForm_eval
    (T : AffineTransfer) (y : ℕ) :
    T.endpointDefect y = -T.displacementForm.eval (y : ℤ) := rfl

/-- Realization turns start evaluation into scaled actual displacement. -/
theorem Realizes.startDefect_eq_displacement
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y) :
    T.startDefect x =
      (T.twoCoeff : ℤ) * ((y : ℤ) - (x : ℤ)) := by
  have hz :
      (T.twoCoeff : ℤ) * (y : ℤ) =
        (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) := by
    exact_mod_cast h
  calc
    T.startDefect x
        = (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) -
            (T.twoCoeff : ℤ) * (x : ℤ) := by
              simp [startDefect, DisplacementForm.eval,
                displacementForm, determinant]
              ring
    _ = (T.twoCoeff : ℤ) * (y : ℤ) -
          (T.twoCoeff : ℤ) * (x : ℤ) := by rw [← hz]
    _ = (T.twoCoeff : ℤ) * ((y : ℤ) - (x : ℤ)) := by ring

/-- Evaluation at the endpoint has the same displacement with coefficient `C`. -/
theorem Realizes.displacementForm_eval_end
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y) :
    T.displacementForm.eval (y : ℤ) =
      (T.oddCoeff : ℤ) * ((y : ℤ) - (x : ℤ)) := by
  have hz :
      (T.twoCoeff : ℤ) * (y : ℤ) =
        (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) := by
    exact_mod_cast h
  calc
    T.displacementForm.eval (y : ℤ)
        = (T.translate : ℤ) +
            ((T.oddCoeff : ℤ) - (T.twoCoeff : ℤ)) * (y : ℤ) := by
              simp [DisplacementForm.eval, displacementForm, determinant]
    _ = (T.oddCoeff : ℤ) * ((y : ℤ) - (x : ℤ)) := by
          rw [show (T.translate : ℤ) =
              (T.twoCoeff : ℤ) * (y : ℤ) -
                (T.oddCoeff : ℤ) * (x : ℤ) by linarith [hz]]
          ring

/-- Historical endpoint defect is scaled reverse displacement. -/
theorem Realizes.endpointDefect_eq_reverseDisplacement
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y) :
    T.endpointDefect y =
      (T.oddCoeff : ℤ) * ((x : ℤ) - (y : ℤ)) := by
  rw [endpointDefect_eq_neg_displacementForm_eval,
    h.displacementForm_eval_end]
  ring

/-- Same-point composition is the raw displacement-form cocycle. -/
theorem startDefect_followedBy_same_point
    (T U : AffineTransfer)
    (x : ℕ) :
    (T.followedBy U).startDefect x =
      (U.oddCoeff : ℤ) * T.startDefect x +
        (T.twoCoeff : ℤ) * U.startDefect x := by
  change
    (T.followedBy U).displacementForm.eval (x : ℤ) = _
  simpa [startDefect] using
    T.displacementForm_eval_followedBy U (x : ℤ)

/--
On an actual composition the intermediate boundary converts the raw cocycle to
an exact transported-displacement sum.
-/
theorem Realizes.startDefect_followedBy
    {T U : AffineTransfer} {x y z : ℕ}
    (hT : T.Realizes x y)
    (hU : U.Realizes y z) :
    (T.followedBy U).startDefect x =
      (U.twoCoeff : ℤ) * T.startDefect x +
        (T.twoCoeff : ℤ) * U.startDefect y := by
  rw [(hT.followedBy hU).startDefect_eq_displacement,
    hT.startDefect_eq_displacement,
    hU.startDefect_eq_displacement]
  simp only [followedBy_twoCoeff]
  push_cast
  ring

/-- Endpoint defect has the dual transported-sum law. -/
theorem Realizes.endpointDefect_followedBy
    {T U : AffineTransfer} {x y z : ℕ}
    (hT : T.Realizes x y)
    (hU : U.Realizes y z) :
    (T.followedBy U).endpointDefect z =
      (U.oddCoeff : ℤ) * T.endpointDefect y +
        (T.oddCoeff : ℤ) * U.endpointDefect z := by
  rw [(hT.followedBy hU).endpointDefect_eq_reverseDisplacement,
    hT.endpointDefect_eq_reverseDisplacement,
    hU.endpointDefect_eq_reverseDisplacement]
  simp only [followedBy_oddCoeff]
  push_cast
  ring

end AffineTransfer

namespace Word

/-- Word start defect is evaluation of the word transfer displacement form. -/
def startDefect (w : Word) (x : ℕ) : ℤ :=
  (AffineTransfer.ofWord w).startDefect x

/-- Word endpoint defect. -/
def endpointDefect (w : Word) (y : ℕ) : ℤ :=
  (AffineTransfer.ofWord w).endpointDefect y

/-- Actual realization: positive return iff positive start evaluation. -/
theorem Realizes.start_lt_end_iff_startDefect_pos
    {w : Word} {x y : ℕ}
    (h : Realizes w x y) :
    x < y ↔ 0 < startDefect w x := by
  have hA :
      (0 : ℤ) < ((AffineTransfer.ofWord w).twoCoeff : ℤ) := by
    change (0 : ℤ) < ((2 ^ twoSteps w : ℕ) : ℤ)
    exact_mod_cast (Nat.pow_pos (by omega : 0 < (2 : ℕ)) : 0 < 2 ^ twoSteps w)
  have hT : (AffineTransfer.ofWord w).Realizes x y := h
  have hdef := hT.startDefect_eq_displacement
  change x < y ↔ 0 < (AffineTransfer.ofWord w).startDefect x
  rw [hdef]
  constructor
  · intro hxy
    have hdiff : (0 : ℤ) < (y : ℤ) - (x : ℤ) := by omega
    exact Int.mul_pos hA hdiff
  · intro hpos
    by_contra hnot
    have hdiff : (y : ℤ) - (x : ℤ) ≤ 0 := by omega
    have hnonpos :
        ((AffineTransfer.ofWord w).twoCoeff : ℤ) *
            ((y : ℤ) - (x : ℤ)) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hdiff
    omega

/-- Actual realization: strict descent iff positive reverse endpoint defect. -/
theorem Realizes.end_lt_start_iff_endpointDefect_pos
    {w : Word} {x y : ℕ}
    (h : Realizes w x y) :
    y < x ↔ 0 < endpointDefect w y := by
  have hC :
      (0 : ℤ) < ((AffineTransfer.ofWord w).oddCoeff : ℤ) := by
    change (0 : ℤ) < ((3 ^ oddSteps w : ℕ) : ℤ)
    exact_mod_cast (Nat.pow_pos (by omega : 0 < (3 : ℕ)) : 0 < 3 ^ oddSteps w)
  have hT : (AffineTransfer.ofWord w).Realizes x y := h
  have hdef := hT.endpointDefect_eq_reverseDisplacement
  change y < x ↔ 0 < (AffineTransfer.ofWord w).endpointDefect y
  rw [hdef]
  constructor
  · intro hyx
    have hdiff : (0 : ℤ) < (x : ℤ) - (y : ℤ) := by omega
    exact Int.mul_pos hC hdiff
  · intro hpos
    by_contra hnot
    have hdiff : (x : ℤ) - (y : ℤ) ≤ 0 := by omega
    have hnonpos :
        ((AffineTransfer.ofWord w).oddCoeff : ℤ) *
            ((x : ℤ) - (y : ℤ)) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (le_of_lt hC) hdiff
    omega

/-- PositiveReturn is realization plus positive displacement evaluation. -/
def PositiveReturn (w : Word) (x y : ℕ) : Prop :=
  Realizes w x y ∧ 0 < startDefect w x

/-- PositiveReturn is exactly the historical strict actual return. -/
theorem positiveReturn_iff
    {w : Word} {x y : ℕ} :
    PositiveReturn w x y ↔ Realizes w x y ∧ x < y := by
  constructor
  · rintro ⟨hreal, hdef⟩
    exact ⟨hreal, (hreal.start_lt_end_iff_startDefect_pos).2 hdef⟩
  · rintro ⟨hreal, hxy⟩
    exact ⟨hreal, (hreal.start_lt_end_iff_startDefect_pos).1 hxy⟩

end Word
end Collatz2
