import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacket
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalContinuedFractionOrientation
import Mathlib.Tactic.Ring

/-!
# Close the elementary corrected Christoffel packet

parity orientation を持つ actual convergent data から、既存
`CriticalChristoffelPacket` の二つの field

* `Q_odd`
* `exact_nonnegative_excluded`

を elementary integer arithmetic で構成する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

private def IsOddInt (z : ℤ) : Prop :=
  ∃ k : ℤ, z = 2 * k + 1

private theorem isOddInt_not_two_dvd
    {z : ℤ}
    (h : IsOddInt z) :
    ¬ (2 : ℤ) ∣ z := by
  intro hd
  rcases h with ⟨a, ha⟩
  rcases hd with ⟨b, hb⟩
  rw [ha] at hb
  omega

private theorem threePow_isOddInt (n : ℕ) :
    IsOddInt ((3 : ℤ) ^ n) := by
  induction n with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ n ih =>
      rcases ih with ⟨k, hk⟩
      refine ⟨3 * k + 1, ?_⟩
      rw [pow_succ, hk]
      ring

private theorem twoPow_even_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    ∃ k : ℤ, (2 : ℤ) ^ n = 2 * k := by
  cases n with
  | zero => omega
  | succ n =>
      refine ⟨(2 : ℤ) ^ n, ?_⟩
      rw [pow_succ]
      ring

private theorem odd_sub_even_isOddInt
    {a b : ℤ}
    (ha : IsOddInt a)
    (hb : ∃ k : ℤ, b = 2 * k) :
    IsOddInt (a - b) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  refine ⟨u - v, ?_⟩
  rw [hu, hv]
  ring

private theorem even_sub_odd_isOddInt
    {a b : ℤ}
    (ha : ∃ k : ℤ, a = 2 * k)
    (hb : IsOddInt b) :
    IsOddInt (a - b) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  refine ⟨u - v - 1, ?_⟩
  rw [hu, hv]
  ring

private theorem odd_mul_isOddInt
    {a b : ℤ}
    (ha : IsOddInt a)
    (hb : IsOddInt b) :
    IsOddInt (a * b) := by
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  refine ⟨2 * u * v + u + v, ?_⟩
  rw [hu, hv]
  ring

private theorem correctedOddQ_isOddInt
    {D : CriticalContinuedFractionData}
    {j : ℕ}
    (hq : 0 < D.q j) :
    IsOddInt
      ((3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j) := by
  exact odd_sub_even_isOddInt
    (threePow_isOddInt (D.p j))
    (twoPow_even_of_pos hq)

private theorem correctedEvenQ_isOddInt
    {D : CriticalContinuedFractionData}
    {j : ℕ}
    (hq : 0 < D.q j) :
    IsOddInt
      (3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j)) := by
  have hthree : IsOddInt (3 : ℤ) := ⟨1, by norm_num⟩
  have hdiff :
      IsOddInt ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) :=
    even_sub_odd_isOddInt
      (twoPow_even_of_pos hq)
      (threePow_isOddInt (D.p j))
  exact odd_mul_isOddInt hthree hdiff

private theorem christoffelTerm_pos
    (p q i : ℕ) :
    0 <
      (3 : ℤ) ^ (p - 1 - i) *
        (2 : ℤ) ^ ((i * q) / p) := by
  positivity

private theorem foldl_positive_terms_nonneg
    (xs : List ℕ)
    (p q : ℕ)
    (a : ℤ)
    (ha : 0 ≤ a) :
    0 ≤
      xs.foldl
        (fun acc i =>
          acc +
            (3 : ℤ) ^ (p - 1 - i) *
              (2 : ℤ) ^ ((i * q) / p))
        a := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hx := christoffelTerm_pos p q x
      omega

/-- explicit Christoffel affine numerator is positive for positive height. -/
theorem criticalChristoffelPhi_pos
    {p q : ℕ}
    (hp : 0 < p) :
    0 < criticalChristoffelPhi p q := by
  cases p with
  | zero => omega
  | succ n =>
      unfold criticalChristoffelPhi
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hprefix :
          0 ≤
            (List.range n).foldl
              (fun acc i =>
                acc +
                  (3 : ℤ) ^ (n + 1 - 1 - i) *
                    (2 : ℤ) ^ ((i * q) / (n + 1)))
              0 := by
        exact foldl_positive_terms_nonneg
          (List.range n) (n + 1) q 0 (by omega)
      have hlast := christoffelTerm_pos (n + 1) q n
      omega

private theorem twoPow_modThree
    (n : ℕ) :
    (∃ k : ℤ, (2 : ℤ) ^ n = 3 * k + 1) ∨
      (∃ k : ℤ, (2 : ℤ) ^ n = 3 * k + 2) := by
  induction n with
  | zero =>
      exact Or.inl ⟨0, by norm_num⟩
  | succ n ih =>
      rcases ih with h | h
      · rcases h with ⟨k, hk⟩
        right
        refine ⟨2 * k, ?_⟩
        rw [pow_succ, hk]
        ring
      · rcases h with ⟨k, hk⟩
        left
        refine ⟨2 * k + 1, ?_⟩
        rw [pow_succ, hk]
        ring

private theorem three_not_dvd_twoPow
    (n : ℕ) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ n := by
  intro hd
  rcases hd with ⟨a, ha⟩
  rcases twoPow_modThree n with h | h
  · rcases h with ⟨b, hb⟩
    rw [hb] at ha
    omega
  · rcases h with ⟨b, hb⟩
    rw [hb] at ha
    omega

private theorem correctedEvenP_not_three_dvd
    (D : CriticalContinuedFractionData)
    {j : ℕ}
    (hjEven : j % 2 = 0) :
    ¬ (3 : ℤ) ∣ correctedChristoffelP D j := by
  rw [correctedChristoffelP_even D hjEven]
  intro hd
  rcases hd with ⟨k, hk⟩
  apply three_not_dvd_twoPow (D.q j - 1)
  refine ⟨k + criticalChristoffelPhiAt D j, ?_⟩
  nlinarith

namespace OrientedCriticalContinuedFractionData

/-- orientation data closes the explicit corrected Christoffel packet. -/
theorem toCriticalChristoffelPacket
    (D : OrientedCriticalContinuedFractionData) :
    CriticalChristoffelPacket D.base := by
  refine {
    Q_odd := ?_
    exact_nonnegative_excluded := ?_
  }
  · intro j
    have hq : 0 < D.base.q j := D.q_pos_all j
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · rw [correctedChristoffelQ_odd D.base hjOdd]
      exact isOddInt_not_two_dvd (correctedOddQ_isOddInt hq)
    · have hjEven : j % 2 = 0 := by omega
      rw [correctedChristoffelQ_even D.base hjEven]
      exact isOddInt_not_two_dvd (correctedEvenQ_isOddInt hq)
  · intro j
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · have hp : 0 < D.base.p j := D.odd_p_pos j hjOdd
      have hP : 0 < correctedChristoffelP D.base j := by
        rw [correctedChristoffelP_odd D.base hjOdd]
        exact criticalChristoffelPhi_pos hp
      have hQ : 0 < correctedChristoffelQ D.base j := by
        rw [correctedChristoffelQ_odd D.base hjOdd]
        exact D.odd_gap_pos hjOdd
      exact LopezStollInstantiation.exactExcluded_of_positive_branch hP hQ
    · have hjEven : j % 2 = 0 := by omega
      have hQ3 : (3 : ℤ) ∣ correctedChristoffelQ D.base j := by
        rw [correctedChristoffelQ_even D.base hjEven]
        exact ⟨(2 : ℤ) ^ D.base.q j - (3 : ℤ) ^ D.base.p j, rfl⟩
      have hP3 : ¬ (3 : ℤ) ∣ correctedChristoffelP D.base j :=
        correctedEvenP_not_three_dvd D.base hjEven
      exact LopezStollInstantiation.exactExcluded_of_modThree_branch hQ3 hP3

end OrientedCriticalContinuedFractionData

end ExternalArithmetic
end CSTMicro
end Collatz2
