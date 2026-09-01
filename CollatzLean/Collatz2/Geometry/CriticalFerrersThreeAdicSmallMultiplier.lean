import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicCore

/-!
# Collatz2 Geometry: 臨界 corridor と小さい collision multiplier

`CriticalFerrersThreeAdicCore` の補題A/Bに、critical roof

  h_j <= criticalHeight j

を重ねる。

最初の相違列 `j` で

  a = min (h j) (h' j)

とすると、strict increasing geometry から

  j <= a < criticalHeight j

が得られる。

さらに `|q| < 8` の collision multiplier では、
`j >= 2` を仮定すると exact 2冪は `a = 2` に固定され、

  j = 2,
  {h 2, h' 2} = {2,3},
  |q| = 4

まで落ちる。
-/

namespace Collatz2
namespace Word

/-- strict increasing な自然数列では index は高さ以下。 -/
theorem index_le_of_strictMono_nat
    {h : ℕ → ℕ}
    (hStrict : StrictMono h)
    (j : ℕ) :
    j ≤ h j := by
  induction j with
  | zero =>
      omega
  | succ j ih =>
      have hStep : h j < h (j + 1) :=
        hStrict (Nat.lt_succ_self j)
      omega

/--
補題Bの幾何側。

最初に異なる列 `j` の低い高さ `a` は index 以上であり、
もう一方の高さも同じ critical roof の下に必要なので roof より strict に低い。

  j <= a < criticalHeight j.
-/
theorem firstDifference_index_bounds_of_collision
    {j a : ℕ}
    {h h' : ℕ → ℕ}
    (hStrict : StrictMono h)
    (hStrict' : StrictMono h')
    (hNe : h j ≠ h' j)
    (ha : a = min (h j) (h' j))
    (hRoof : h j ≤ criticalHeight j)
    (hRoof' : h' j ≤ criticalHeight j) :
    j ≤ a ∧ a < criticalHeight j := by
  have hjh : j ≤ h j := index_le_of_strictMono_nat hStrict j
  have hjh' : j ≤ h' j := index_le_of_strictMono_nat hStrict' j
  constructor
  · rw [ha]
    exact (Nat.le_min).2 ⟨hjh, hjh'⟩
  · rcases lt_or_gt_of_ne hNe with hlt | hgt
    · have haEq : a = h j := by
        rw [ha, Nat.min_eq_left (Nat.le_of_lt hlt)]
      omega
    · have haEq : a = h' j := by
        rw [ha, Nat.min_eq_right (Nat.le_of_lt hgt)]
      omega

/-- `criticalHeight 2 = 3` を後段から直接使うための小補題。 -/
@[simp] theorem criticalHeight_two :
    criticalHeight 2 = 3 := by decide

/--
小さい nonzero multiplier の exact 2冪が `a` なら、`2 <= a` のもとで `a = 2`。

ここでは `|q| < 8` を `q.natAbs < 8` として扱う。
-/
theorem exactTwoPow_eq_two_of_natAbs_lt_eight
    {a : ℕ}
    {q : ℤ}
    (haTwo : 2 ≤ a)
    (hqNe : q ≠ 0)
    (hqSmall : q.natAbs < 8)
    (hExact : ExactTwoPowZ a q) :
    a = 2 ∧ q.natAbs = 4 := by
  have hDivAbs : 2 ^ a ∣ q.natAbs := by
    rw [← Int.natCast_dvd]
    simpa using hExact.1
  have hAbsPos : 0 < q.natAbs :=
    Int.natAbs_pos.mpr hqNe
  have hPowLe : 2 ^ a ≤ q.natAbs :=
    Nat.le_of_dvd hAbsPos hDivAbs
  have haLe : a ≤ 2 := by
    by_contra hnot
    have haThree : 3 ≤ a := by omega
    have hEightLePow : 8 ≤ 2 ^ a := by
      calc
        8 = 2 ^ (3 : ℕ) := by norm_num
        _ ≤ 2 ^ a :=
          Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) haThree
    omega
  have haEq : a = 2 := by omega
  subst a
  have hFourDiv : 4 ∣ q.natAbs := by
    simpa using hDivAbs
  rcases hFourDiv with ⟨t, ht⟩
  have htPos : 0 < t := by
    by_contra ht0
    have htZero : t = 0 := by omega
    rw [htZero] at ht
    simp at ht
    omega
  have htOne : t = 1 := by
    omega
  rw [htOne] at ht
  norm_num at ht ⊢
  exact ht

/--
`|q| = 4` の Int 表現。
-/
theorem eq_four_or_neg_four_of_natAbs_eq_four
    {q : ℤ}
    (hAbs : q.natAbs = 4) :
    q = 4 ∨ q = -4 := by
  cases q with
  | ofNat n =>
      left
      simp at hAbs ⊢
      omega
  | negSucc n =>
      right
      simp at hAbs ⊢
      omega

/--
`|q| < 8` の collision で、最初の相違が column 2 以降にある場合の具体形。

結論は

  q = ±4,
  a = 2,
  j = 2,
  (h 2, h' 2) = (2,3) または (3,2)

まで固定される。
-/
theorem firstDifference_eq_two_of_multiplier_abs_lt_eight
    {r j a : ℕ}
    {h h' : ℕ → ℕ}
    {q : ℤ}
    (hjLt : j < r)
    (hjTwo : 2 ≤ j)
    (hBefore : ∀ i : ℕ, i < j → h i = h' i)
    (hNe : h j ≠ h' j)
    (ha : a = min (h j) (h' j))
    (hAfter :
      ∀ i : ℕ, j < i → i < r →
        a < h i ∧ a < h' i)
    (hStrict : StrictMono h)
    (hStrict' : StrictMono h')
    (hRoof : h j ≤ criticalHeight j)
    (hRoof' : h' j ≤ criticalHeight j)
    (hCollision :
      criticalFerrersCodeDiffZ r h h' =
        q * (3 : ℤ) ^ r)
    (hqNe : q ≠ 0)
    (hqSmall : q.natAbs < 8) :
    (q = 4 ∨ q = -4) ∧
      a = 2 ∧
      j = 2 ∧
      ((h 2 = 2 ∧ h' 2 = 3) ∨
        (h 2 = 3 ∧ h' 2 = 2)) := by
  have hA : ExactTwoPowZ a (criticalFerrersCodeDiffZ r h h') :=
    firstDifference_twoPow_exact
      hjLt hBefore hNe ha hAfter
  have hB : ExactTwoPowZ a q :=
    collisionMultiplier_twoPow_exact hA hCollision
  have hBounds : j ≤ a ∧ a < criticalHeight j :=
    firstDifference_index_bounds_of_collision
      hStrict hStrict' hNe ha hRoof hRoof'
  have haTwo : 2 ≤ a := by omega
  obtain ⟨haEq, hqAbs⟩ :=
    exactTwoPow_eq_two_of_natAbs_lt_eight
      haTwo hqNe hqSmall hB
  have hjEq : j = 2 := by
    omega
  have hqCases : q = 4 ∨ q = -4 :=
    eq_four_or_neg_four_of_natAbs_eq_four hqAbs
  subst j
  have hRoof2 : h 2 ≤ 3 := by
    simpa using hRoof
  have hRoof2' : h' 2 ≤ 3 := by
    simpa using hRoof'
  have haMin : 2 = min (h 2) (h' 2) := by
    exact haEq.symm.trans ha
  have hPair :
      (h 2 = 2 ∧ h' 2 = 3) ∨
        (h 2 = 3 ∧ h' 2 = 2) := by
    rcases lt_or_gt_of_ne hNe with hlt | hgt
    · left
      have hLow : h 2 = 2 := by
        have hMin :
            min (h 2) (h' 2) = h 2 :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        omega
      constructor
      · exact hLow
      · omega
    · right
      have hLow : h' 2 = 2 := by
        have hMin :
            min (h 2) (h' 2) = h' 2 :=
          Nat.min_eq_right (Nat.le_of_lt hgt)
        omega
      constructor
      · omega
      · exact hLow
  exact ⟨hqCases, haEq, rfl, hPair⟩

end Word
end Collatz2
