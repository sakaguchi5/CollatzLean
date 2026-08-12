import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Local.DeterminantSign


/-!
# Collatz2: signed displacement defect

Defect は新しい trajectory data ではなく affine transfer の評価である。

start 側では

  `B + (C-A)x = A(y-x)`

endpoint 側では

  `(A-C)y - B = C(x-y)`

となる。したがって return / descent の符号は defect の符号のコロラリーになる。
-/

namespace Collatz2

namespace AffineTransfer

/-- start `x` で評価した signed displacement defect。 -/
def startDefect (T : AffineTransfer) (x : ℕ) : ℤ :=
  (T.translate : ℤ) + T.determinant * (x : ℤ)

/-- endpoint `y` で評価した signed endpoint defect。 -/
def endpointDefect (T : AffineTransfer) (y : ℕ) : ℤ :=
  (-T.determinant) * (y : ℤ) - (T.translate : ℤ)

/-- realization 上では start defect は scaled displacement そのもの。 -/
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
              simp [startDefect, determinant]
              ring
    _ = (T.twoCoeff : ℤ) * (y : ℤ) -
          (T.twoCoeff : ℤ) * (x : ℤ) := by rw [← hz]
    _ = (T.twoCoeff : ℤ) * ((y : ℤ) - (x : ℤ)) := by ring

/-- realization 上では endpoint defect も scaled reverse displacement。 -/
theorem Realizes.endpointDefect_eq_reverseDisplacement
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y) :
    T.endpointDefect y =
      (T.oddCoeff : ℤ) * ((x : ℤ) - (y : ℤ)) := by
  have hz :
      (T.twoCoeff : ℤ) * (y : ℤ) =
        (T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ) := by
    exact_mod_cast h
  calc
    T.endpointDefect y
        = (T.twoCoeff : ℤ) * (y : ℤ) -
            (T.oddCoeff : ℤ) * (y : ℤ) - (T.translate : ℤ) := by
              simp [endpointDefect, determinant]
              ring
    _ = (T.oddCoeff : ℤ) * (x : ℤ) -
          (T.oddCoeff : ℤ) * (y : ℤ) := by
              rw [hz]
              ring
    _ = (T.oddCoeff : ℤ) * ((x : ℤ) - (y : ℤ)) := by ring

/--
realized composition の start defect は二つの局所 defect の transported sum。
これは prepend-one や return balance の上位 cocycle law。
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

/-- endpoint defect にも双対な transported-sum law がある。 -/
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

/-- word start で評価した defect。 -/
def startDefect (w : Word) (x : ℕ) : ℤ :=
  (AffineTransfer.ofWord w).startDefect x

/-- word endpoint で評価した defect。 -/
def endpointDefect (w : Word) (y : ℕ) : ℤ :=
  (AffineTransfer.ofWord w).endpointDefect y

/-- actual realization では positive return と positive start defect は同値。 -/
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

/-- actual realization では strict descent と positive endpoint defect は同値。 -/
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

/--
PositiveReturn は新しい data ではなく、realization と start-defect の正符号の合成命題。
-/
def PositiveReturn (w : Word) (x y : ℕ) : Prop :=
  Realizes w x y ∧ 0 < startDefect w x

/-- PositiveReturn は従来の actual `x < y` と exact に同値。 -/
theorem positiveReturn_iff
    {w : Word} {x y : ℕ} :
    PositiveReturn w x y ↔ Realizes w x y ∧ x < y := by
  constructor
  · rintro ⟨hreal, hdef⟩
    exact ⟨hreal, (hreal.start_lt_end_iff_startDefect_pos).2 hdef⟩
  · rintro ⟨hreal, hxy⟩
    exact ⟨hreal, (hreal.start_lt_end_iff_startDefect_pos).1 hxy⟩

end Word

namespace Runs

/-- stepwise run 上の start defect は actual displacement を exact に測る。 -/
theorem startDefect_eq_displacement
    {w : Word} {x y : ℕ}
    (h : Runs w x y) :
    Word.startDefect w x =
      ((AffineTransfer.ofWord w).twoCoeff : ℤ) *
        ((y : ℤ) - (x : ℤ)) :=
by
  have hT : (AffineTransfer.ofWord w).Realizes x y := h.realizes
  exact hT.startDefect_eq_displacement

end Runs
end Collatz2
