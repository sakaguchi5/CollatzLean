import CollatzLean.Collatz2.Core.Interval

/-!
# Collatz2: determinant sign

`Expanding` / `Contracting` を primitive な word 分類として置かず、
affine transfer の signed determinant の正負から導出する。

valid 非空 Collatz word では `3^p` は奇数、`2^H` は偶数なので
 determinant は0にならない。したがって符号は必ず正または負の二値になる。
-/

namespace Collatz2

namespace AffineTransfer

/-- determinant が正。 -/
def PositiveDeterminant (T : AffineTransfer) : Prop :=
  0 < T.determinant

/-- determinant が負。 -/
def NegativeDeterminant (T : AffineTransfer) : Prop :=
  T.determinant < 0

end AffineTransfer

namespace Word

/-- `Expanding` は word transfer の determinant が正であることの別名。 -/
def Expanding (w : Word) : Prop :=
  AffineTransfer.PositiveDeterminant (AffineTransfer.ofWord w)

/-- `Contracting` は word transfer の determinant が負であることの別名。 -/
def Contracting (w : Word) : Prop :=
  AffineTransfer.NegativeDeterminant (AffineTransfer.ofWord w)

/-- valid 非空 word の determinant は0にならない。 -/
theorem determinant_ne_zero_of_valid_nonempty
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    (AffineTransfer.ofWord w).determinant ≠ 0 := by
  intro hzero
  have hEqZ :
      (3 : ℤ) ^ oddSteps w =
        (2 : ℤ) ^ twoSteps w := by
    have hdet := AffineTransfer.determinant_ofWord w
    rw [hzero] at hdet
    omega
  have hEqN :
      3 ^ oddSteps w = 2 ^ twoSteps w := by
    exact_mod_cast hEqZ
  have hH : 0 < twoSteps w :=
    twoSteps_pos_of_valid_nonempty hvalid hne
  have hOdd : Odd (3 ^ oddSteps w) :=
    (show Odd (3 : ℕ) by decide).pow
  have hEven : Even (2 ^ twoSteps w) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hH)
  rcases hOdd with ⟨a, ha⟩
  rcases hEven with ⟨b, hb⟩
  rw [hEqN] at ha
  omega

/-- valid 非空 word の determinant sign は正または負。 -/
theorem positive_or_negative_determinant_of_valid_nonempty
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    AffineTransfer.PositiveDeterminant (AffineTransfer.ofWord w) ∨
      AffineTransfer.NegativeDeterminant (AffineTransfer.ofWord w) := by
  have hneDet := determinant_ne_zero_of_valid_nonempty hvalid hne
  rcases lt_trichotomy
      0 (AffineTransfer.ofWord w).determinant with hpos | hzero | hneg
  · exact Or.inl hpos
  · exact False.elim (hneDet hzero.symm)
  · exact Or.inr hneg

/-- Expanding は従来形 `2^H < 3^p` と同値。 -/
theorem expanding_iff_twoPow_lt_threePow
    {w : Word} :
    Expanding w ↔
      2 ^ twoSteps w < 3 ^ oddSteps w := by
  constructor
  · intro h
    unfold Expanding AffineTransfer.PositiveDeterminant at h
    rw [AffineTransfer.determinant_ofWord] at h
    have hz :
        (2 : ℤ) ^ twoSteps w <
          (3 : ℤ) ^ oddSteps w := by
      omega
    exact_mod_cast hz
  · intro h
    unfold Expanding AffineTransfer.PositiveDeterminant
    rw [AffineTransfer.determinant_ofWord]
    have hz :
        (2 : ℤ) ^ twoSteps w <
          (3 : ℤ) ^ oddSteps w := by
      exact_mod_cast h
    omega

/-- Contracting は従来形 `3^p < 2^H` と同値。 -/
theorem contracting_iff_threePow_lt_twoPow
    {w : Word} :
    Contracting w ↔
      3 ^ oddSteps w < 2 ^ twoSteps w := by
  constructor
  · intro h
    unfold Contracting AffineTransfer.NegativeDeterminant at h
    rw [AffineTransfer.determinant_ofWord] at h
    have hz :
        (3 : ℤ) ^ oddSteps w <
          (2 : ℤ) ^ twoSteps w := by
      omega
    exact_mod_cast hz
  · intro h
    unfold Contracting AffineTransfer.NegativeDeterminant
    rw [AffineTransfer.determinant_ofWord]
    have hz :
        (3 : ℤ) ^ oddSteps w <
          (2 : ℤ) ^ twoSteps w := by
      exact_mod_cast h
    omega

/--
第1段階の checkpoint。
valid 非空 word は determinant sign の非零性から
Expanding または Contracting のどちらかへ必ず落ちる。
-/
theorem expanding_or_contracting_of_valid_nonempty
    {w : Word}
    (hvalid : Valid w)
    (hne : w ≠ []) :
    Expanding w ∨ Contracting w := by
  exact positive_or_negative_determinant_of_valid_nonempty hvalid hne

/-- Expanding と Contracting は同時には成立しない。 -/
theorem not_expanding_and_contracting
    (w : Word) :
    ¬ (Expanding w ∧ Contracting w) := by
  intro h
  exact (not_lt_of_ge (le_of_lt h.1)) h.2

end Word
end Collatz2
