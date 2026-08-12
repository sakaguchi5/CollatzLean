import CollatzLean.Collatz2.Local.FirstCrossing


/-!
# Collatz2: suffix determinant profile

suffix gap や all-suffix-contracting を primitive な recursive package として置かず、
各 terminal suffix の signed determinant profile から導出する。
-/

namespace Collatz2
namespace Word

/-- cut `k` 以後の suffix transfer determinant。 -/
def suffixDeterminant (w : Word) (k : ℕ) : ℤ :=
  (AffineTransfer.ofWord (w.drop k)).determinant

/-- 全 nonempty suffix determinant が負。 -/
def AllSuffixesNegativeDeterminant (w : Word) : Prop :=
  ∀ k : ℕ, k < w.length → suffixDeterminant w k < 0

/--
従来名 `AllSuffixesContracting` は suffix determinant profile の負性の別名。
-/
def AllSuffixesContracting (w : Word) : Prop :=
  AllSuffixesNegativeDeterminant w

/-- suffix determinant が負であることはその suffix が Contracting であること。 -/
theorem suffixDeterminant_neg_iff_contracting
    {w : Word} {k : ℕ} :
    suffixDeterminant w k < 0 ↔ Contracting (w.drop k) := by
  rfl

/--
first crossing の terminal suffix はすべて determinant negative。

whole determinant の factorization

`det(uv) = C(v) det(u) + A(u) det(v)`

と proper prefix の正符号から直接従う。
-/
theorem FirstCrossing.allSuffixesNegativeDeterminant
    {w : Word}
    (hF : FirstCrossing w) :
    AllSuffixesNegativeDeterminant w := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [suffixDeterminant]
    change (AffineTransfer.ofWord w).NegativeDeterminant
    exact hF.terminalNegative
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hPrefix :
        AffineTransfer.PositiveDeterminant
          (AffineTransfer.ofWord (w.take k)) :=
      hF.properPositive k hkPos hk
    have hTransfer :
        AffineTransfer.ofWord w =
          (AffineTransfer.ofWord (w.take k)).followedBy
            (AffineTransfer.ofWord (w.drop k)) := by
      rw [← AffineTransfer.ofWord_append]
      exact congrArg AffineTransfer.ofWord (List.take_append_drop k w).symm
    have hFactor :
        (AffineTransfer.ofWord w).determinant =
          ((AffineTransfer.ofWord (w.drop k)).oddCoeff : ℤ) *
              (AffineTransfer.ofWord (w.take k)).determinant +
            ((AffineTransfer.ofWord (w.take k)).twoCoeff : ℤ) *
              (AffineTransfer.ofWord (w.drop k)).determinant := by
      rw [hTransfer]
      exact AffineTransfer.determinant_followedBy _ _
    by_contra hnot
    have hSuffixNonneg :
        0 ≤ (AffineTransfer.ofWord (w.drop k)).determinant := by
      change ¬ (AffineTransfer.ofWord (w.drop k)).determinant < 0 at hnot
      omega
    have hOddPos :
        (0 : ℤ) < ((AffineTransfer.ofWord (w.drop k)).oddCoeff : ℤ) := by
      change (0 : ℤ) < ((3 ^ oddSteps (w.drop k) : ℕ) : ℤ)
      exact_mod_cast
        (Nat.pow_pos (by omega : 0 < (3 : ℕ)) :
          0 < 3 ^ oddSteps (w.drop k))
    have hTwoPos :
        (0 : ℤ) < ((AffineTransfer.ofWord (w.take k)).twoCoeff : ℤ) := by
      change (0 : ℤ) < ((2 ^ twoSteps (w.take k) : ℕ) : ℤ)
      exact_mod_cast
        (Nat.pow_pos (by omega : 0 < (2 : ℕ)) :
          0 < 2 ^ twoSteps (w.take k))
    have hFirstPos :
        0 < ((AffineTransfer.ofWord (w.drop k)).oddCoeff : ℤ) *
          (AffineTransfer.ofWord (w.take k)).determinant :=
      Int.mul_pos hOddPos hPrefix
    have hSecondNonneg :
        0 ≤ ((AffineTransfer.ofWord (w.take k)).twoCoeff : ℤ) *
          (AffineTransfer.ofWord (w.drop k)).determinant :=
      Int.mul_nonneg (le_of_lt hTwoPos) hSuffixNonneg
    have hWholePos :
        0 < (AffineTransfer.ofWord w).determinant := by
      rw [hFactor]
      exact add_pos_of_pos_of_nonneg hFirstPos hSecondNonneg
    exact (not_lt_of_ge (le_of_lt hF.terminalNegative)) hWholePos

/-- first crossing なら従来名でも全 nonempty suffix が Contracting。 -/
theorem FirstCrossing.allSuffixesContracting
    {w : Word}
    (hF : FirstCrossing w) :
    AllSuffixesContracting w :=
  hF.allSuffixesNegativeDeterminant

/-- contracting suffix の natural gap は signed determinant の絶対方向。 -/
def suffixGap (w : Word) (k : ℕ) : ℕ :=
  2 ^ twoSteps (w.drop k) - 3 ^ oddSteps (w.drop k)

/-- profile が負なら対応する suffix gap は正。 -/
theorem suffixGap_pos_of_negative
    {w : Word} {k : ℕ}
    (hneg : suffixDeterminant w k < 0) :
    0 < suffixGap w k := by
  have hpow :
      3 ^ oddSteps (w.drop k) < 2 ^ twoSteps (w.drop k) := by
    have hC : Contracting (w.drop k) :=
      (suffixDeterminant_neg_iff_contracting).1 hneg
    exact (contracting_iff_threePow_lt_twoPow).1 hC
  exact Nat.sub_pos_of_lt hpow

end Word
end Collatz2
