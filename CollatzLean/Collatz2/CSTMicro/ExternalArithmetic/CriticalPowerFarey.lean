import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalContinuedFractionOrientation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

set_option linter.style.nativeDecide false

/-!
# Critical slope の exact power-Farey convergents

`log 2 / log 3` を実数 continued fraction として展開する代わりに、

  below(p/q) : 3^p < 2^q
  above(p/q) : 2^q < 3^p

という exact power language で Stern--Brocot/Farey convergent を構成する。

consecutive pair `(a,b)` は critical slope を挟む Farey neighbors で、
`a + t b` が `a` 側にある最大の正整数 `t` を取って次の convergent とする。
この定義は ordinary regular continued fraction と同じ convergent 列を与えるが、
後段ではその同定自体は不要で、Farey adjacency と power orientation だけを使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

@[ext]
structure CriticalPowerFraction where
  p : ℕ
  q : ℕ
  q_pos : 0 < q

namespace CriticalPowerFraction

noncomputable instance : DecidableEq CriticalPowerFraction :=
  Classical.decEq _

/-- critical slope より下。 -/
def Below (x : CriticalPowerFraction) : Prop :=
  3 ^ x.p < 2 ^ x.q

/-- critical slope より上。 -/
def Above (x : CriticalPowerFraction) : Prop :=
  2 ^ x.q < 3 ^ x.p

instance (x : CriticalPowerFraction) : Decidable x.Below := by
  unfold Below
  infer_instance

instance (x : CriticalPowerFraction) : Decidable x.Above := by
  unfold Above
  infer_instance

/-- Farey linear combination `a + t b`。 -/
def combine
    (a b : CriticalPowerFraction)
    (t : ℕ) : CriticalPowerFraction := {
  p := a.p + t * b.p
  q := a.q + t * b.q
  q_pos := by
    exact Nat.add_pos_left a.q_pos (t * b.q)
}

@[simp] theorem combine_p
    (a b : CriticalPowerFraction) (t : ℕ) :
    (combine a b t).p = a.p + t * b.p := rfl

@[simp] theorem combine_q
    (a b : CriticalPowerFraction) (t : ℕ) :
    (combine a b t).q = a.q + t * b.q := rfl

/-- determinant の絶対値が 1 であることの Nat 版。 -/
def FareyAdjacent
    (a b : CriticalPowerFraction) : Prop :=
  a.p * b.q + 1 = b.p * a.q ∨
    b.p * a.q + 1 = a.p * b.q

/-- positive exponents では 2 冪と 3 冪は一致しない。 -/
theorem twoPow_ne_threePow_of_pos
    {p q : ℕ}
    (hq : 0 < q) :
    2 ^ q ≠ 3 ^ p := by
  intro h
  have h2 : (2 ^ q) % 2 = 0 := by
    cases q with
    | zero => omega
    | succ n =>
        rw [pow_succ]
        simp
  have h3 : (3 ^ p) % 2 = 1 := by
    simp [Nat.pow_mod]
  rw [h] at h2
  omega

/-- positive fraction は critical slope の上下どちらかに必ずある。 -/
theorem below_or_above_of_pos
    (x : CriticalPowerFraction) :
    x.Below ∨ x.Above := by
  unfold Below Above
  have hne := twoPow_ne_threePow_of_pos (p := x.p) x.q_pos
  omega

/-- below fraction は任意の above fraction より小さい。 -/
theorem cross_lt_of_below_above
    {a b : CriticalPowerFraction}
    (ha : a.Below)
    (hb : b.Above) :
    a.p * b.q < b.p * a.q := by
  unfold Below at ha
  unfold Above at hb
  by_contra hnot
  have hcross : b.p * a.q ≤ a.p * b.q := by
    omega
  have h3 :
      3 ^ (b.p * a.q) ≤ 3 ^ (a.p * b.q) :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hcross
  have haPow :
      3 ^ (a.p * b.q) < 2 ^ (a.q * b.q) := by
    simpa [pow_mul] using
      Nat.pow_lt_pow_left ha (Nat.ne_of_gt b.q_pos)
  have hbPow :
      2 ^ (b.q * a.q) < 3 ^ (b.p * a.q) := by
    simpa [pow_mul] using
      Nat.pow_lt_pow_left hb (Nat.ne_of_gt a.q_pos)
  have haPow' :
      3 ^ (a.p * b.q) < 2 ^ (b.q * a.q) := by
    simpa [Nat.mul_comm] using haPow
  have hcontra :
      3 ^ (b.p * a.q) < 3 ^ (b.p * a.q) := by
    exact lt_of_le_of_lt h3 (lt_trans haPow' hbPow)
  exact (Nat.lt_irrefl _ hcontra)

/-- below fraction 以下の positive-denominator fraction も below。 -/
theorem below_of_fraction_le_below
    {x y : CriticalPowerFraction}
    (hxy : x.p * y.q ≤ y.p * x.q)
    (hy : y.Below) :
    x.Below := by
  by_cases hxp : x.p = 0
  · unfold Below
    rw [hxp]
    simp only [pow_zero, Nat.one_lt_two_pow_iff, ne_eq]
    exact Nat.ne_of_gt x.q_pos
  · rcases below_or_above_of_pos x with hx | hx
    · exact hx
    · exfalso
      have hyx := cross_lt_of_below_above hy hx
      exact (Nat.not_lt_of_ge hxy) hyx

/-- above fraction 以上の positive-denominator fraction も above。 -/
theorem above_of_above_le_fraction
    {x y : CriticalPowerFraction}
    (hyx : y.p * x.q ≤ x.p * y.q)
    (hy : y.Above) :
    x.Above := by
  have hyp : 0 < y.p := by
    by_contra h
    have hp0 : y.p = 0 := by
      omega
    unfold Above at hy
    rw [hp0] at hy
    simp at hy
  rcases below_or_above_of_pos x with hx | hx
  · exfalso
    have hxy := cross_lt_of_below_above hx hy
    exact (Nat.not_lt_of_ge hyx) hxy
  · exact hx

/-- Farey neighbors の間に入る positive fraction の denominator は和以上。 -/
theorem denominator_ge_sum_of_between
    {a b x : CriticalPowerFraction}
    (hadj : a.p * b.q + 1 = b.p * a.q)
    (hax : a.p * x.q < x.p * a.q)
    (hxb : x.p * b.q < b.p * x.q) :
    a.q + b.q ≤ x.q := by
  have h1 : 1 ≤ x.p * a.q - a.p * x.q := by omega
  have h2 : 1 ≤ b.p * x.q - x.p * b.q := by omega
  have hd1 :
      (((x.p * a.q - a.p * x.q : ℕ) : ℤ)) =
        (x.p : ℤ) * a.q - (a.p : ℤ) * x.q := by
    rw [Nat.cast_sub (Nat.le_of_lt hax)]
    push_cast
    rfl
  have hd2 :
      (((b.p * x.q - x.p * b.q : ℕ) : ℤ)) =
        (b.p : ℤ) * x.q - (x.p : ℤ) * b.q := by
    rw [Nat.cast_sub (Nat.le_of_lt hxb)]
    push_cast
    rfl
  have hadjZ :
      (a.p : ℤ) * b.q + 1 = (b.p : ℤ) * a.q := by
    exact_mod_cast hadj
  have hidZ :
      (x.q : ℤ) =
        (b.q : ℤ) * (x.p * a.q - a.p * x.q : ℕ) +
          (a.q : ℤ) * (b.p * x.q - x.p * b.q : ℕ) := by
    rw [hd1, hd2]
    nlinarith
  have hid :
      x.q =
        b.q * (x.p * a.q - a.p * x.q) +
          a.q * (b.p * x.q - x.p * b.q) := by
    exact_mod_cast hidZ
  rw [hid]
  have hbq := Nat.mul_le_mul_left b.q h1
  have haq := Nat.mul_le_mul_left a.q h2
  omega

/-- determinant の向きに依らない no-small-denominator version。 -/
theorem denominator_ge_sum_of_strict_between
    {a b x : CriticalPowerFraction}
    (hadj : FareyAdjacent a b)
    (hbetween :
      (a.p * x.q < x.p * a.q ∧
        x.p * b.q < b.p * x.q) ∨
      (b.p * x.q < x.p * b.q ∧
        x.p * a.q < a.p * x.q)) :
    a.q + b.q ≤ x.q := by
  rcases hadj with hadj | hadj
  · rcases hbetween with h | h
    · exact denominator_ge_sum_of_between hadj h.1 h.2
    · exfalso
      have hab :
          a.p * b.q < b.p * a.q := by
        omega
      have h1 :
          a.q * (b.p * x.q) <
            a.q * (x.p * b.q) :=
        (Nat.mul_lt_mul_left a.q_pos).2 h.1
      have h2 :
          b.q * (x.p * a.q) <
            b.q * (a.p * x.q) :=
        (Nat.mul_lt_mul_left b.q_pos).2 h.2
      have hrev :
          (b.p * a.q) * x.q <
            (a.p * b.q) * x.q := by
        calc
          (b.p * a.q) * x.q
              = a.q * (b.p * x.q) := by ac_rfl
          _ < a.q * (x.p * b.q) := h1
          _ = b.q * (x.p * a.q) := by ac_rfl
          _ < b.q * (a.p * x.q) := h2
          _ = (a.p * b.q) * x.q := by ac_rfl
      have hfwd :
          (a.p * b.q) * x.q <
            (b.p * a.q) * x.q :=
        (Nat.mul_lt_mul_right x.q_pos).2 hab
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hfwd)) hrev
  · rcases hbetween with h | h
    · exfalso
      have hba :
          b.p * a.q < a.p * b.q := by
        omega
      have h1 :
          b.q * (a.p * x.q) <
            b.q * (x.p * a.q) :=
        (Nat.mul_lt_mul_left b.q_pos).2 h.1
      have h2 :
          a.q * (x.p * b.q) <
            a.q * (b.p * x.q) :=
        (Nat.mul_lt_mul_left a.q_pos).2 h.2
      have hrev :
          (a.p * b.q) * x.q <
            (b.p * a.q) * x.q := by
        calc
          (a.p * b.q) * x.q
              = b.q * (a.p * x.q) := by ac_rfl
          _ < b.q * (x.p * a.q) := h1
          _ = a.q * (x.p * b.q) := by ac_rfl
          _ < a.q * (b.p * x.q) := h2
          _ = (b.p * a.q) * x.q := by ac_rfl
      have hfwd :
          (b.p * a.q) * x.q <
            (a.p * b.q) * x.q :=
        (Nat.mul_lt_mul_right x.q_pos).2 hba
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hfwd)) hrev
    · have h :=
        denominator_ge_sum_of_between
          (a := b) (b := a) (x := x) hadj h.1 h.2
      simpa [Nat.add_comm] using h

/-- Farey adjacency は linear combination で保存される。 -/
theorem fareyAdjacent_right_combine
    {a b : CriticalPowerFraction}
    (h : FareyAdjacent a b)
    (t : ℕ) :
    FareyAdjacent b (combine a b t) := by
  unfold FareyAdjacent at h ⊢
  rcases h with h | h
  · right
    dsimp [combine]
    nlinarith
  · left
    dsimp [combine]
    nlinarith

/-- `[0,1]` 内性は positive linear combination で保存される。 -/
theorem combine_p_le_q
    {a b : CriticalPowerFraction}
    (ha : a.p ≤ a.q)
    (hb : b.p ≤ b.q)
    (t : ℕ) :
    (combine a b t).p ≤ (combine a b t).q := by
  dsimp [combine]
  exact Nat.add_le_add ha (Nat.mul_le_mul_left t hb)

end CriticalPowerFraction

open CriticalPowerFraction

/--
below `a` と above `b` の pair。
mediant が left/below 側にあることまで保持する。
-/
structure CriticalBelowAboveState where
  left : CriticalPowerFraction
  right : CriticalPowerFraction
  left_below : left.Below
  right_above : right.Above
  adjacent : FareyAdjacent left right
  mediant_left : (combine left right 1).Below
  left_p_pos : 0 < left.p
  right_p_pos : 0 < right.p
  left_p_le_q : left.p ≤ left.q
  right_p_le_q : right.p ≤ right.q
  q_strict : left.q < right.q

/-- above `a` と below `b` の pair。 -/
structure CriticalAboveBelowState where
  left : CriticalPowerFraction
  right : CriticalPowerFraction
  left_above : left.Above
  right_below : right.Below
  adjacent : FareyAdjacent left right
  mediant_left : (combine left right 1).Above
  left_p_pos : 0 < left.p
  right_p_pos : 0 < right.p
  left_p_le_q : left.p ≤ left.q
  right_p_le_q : right.p ≤ right.q
  q_strict : left.q < right.q

private theorem exists_pow_ratio_cross
    {A B C D : ℕ}
    (hA : 0 < A)
    (hB : 0 < B)
    (hC : 0 < C)
    (hD : 0 < D)
    (hDC : D < C) :
    ∃ n : ℕ, A * D ^ n < B * C ^ n := by
  have hRatio : (1 : ℝ) < (C : ℝ) / D := by
    rw [one_lt_div (by exact_mod_cast hD)]
    exact_mod_cast hDC
  have hLogPos : 0 < Real.log ((C : ℝ) / D) :=
    Real.log_pos hRatio
  obtain ⟨n, hn⟩ :=
    exists_nat_gt
      (Real.log ((A : ℝ) / B) /
        Real.log ((C : ℝ) / D))
  have hn' :
      Real.log ((A : ℝ) / B) <
        (n : ℝ) * Real.log ((C : ℝ) / D) := by
    have := (div_lt_iff₀ hLogPos).1 hn
    simpa [mul_comm] using this
  have hABpos : (0 : ℝ) < (A : ℝ) / B := by
    positivity
  have hCDpos : (0 : ℝ) < (C : ℝ) / D := by
    positivity
  have hpowpos : (0 : ℝ) < ((C : ℝ) / D) ^ n := by
    positivity
  have hlogpow :
      Real.log (((C : ℝ) / D) ^ n) =
        (n : ℝ) * Real.log ((C : ℝ) / D) := by
    simp only [Real.log_pow]
  have hrat :
      (A : ℝ) / B < ((C : ℝ) / D) ^ n := by
    apply (Real.log_lt_log_iff hABpos hpowpos).1
    rw [hlogpow]
    exact hn'
  refine ⟨n, ?_⟩
  have hBposR : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hB
  have hDpowposR : (0 : ℝ) < (D : ℝ) ^ n := by
    positivity
  have hrat' :
      (A : ℝ) / B <
        (C : ℝ) ^ n / (D : ℝ) ^ n := by
    simpa [div_pow] using hrat
  have h1 :
      (A : ℝ) <
        ((C : ℝ) ^ n / (D : ℝ) ^ n) * B := by
    exact (div_lt_iff₀ hBposR).1 hrat'
  have h1' :
      (A : ℝ) <
        ((B : ℝ) * (C : ℝ) ^ n) / (D : ℝ) ^ n := by
    calc
      (A : ℝ) <
          ((C : ℝ) ^ n / (D : ℝ) ^ n) * B := h1
      _ = ((B : ℝ) * (C : ℝ) ^ n) / (D : ℝ) ^ n := by
        ring
  have hreal :
      (A : ℝ) * (D : ℝ) ^ n <
        (B : ℝ) * (C : ℝ) ^ n := by
    exact (lt_div_iff₀ hDpowposR).1 h1'
  exact_mod_cast hreal

private theorem exists_above_combine_of_below_above
    (S : CriticalBelowAboveState) :
    ∃ t : ℕ, 1 ≤ t ∧ (combine S.left S.right t).Above := by
  have hCross :=
    exists_pow_ratio_cross
      (A := 2 ^ S.left.q)
      (B := 3 ^ S.left.p)
      (C := 3 ^ S.right.p)
      (D := 2 ^ S.right.q)
      (by positivity) (by positivity) (by positivity) (by positivity) S.right_above
  rcases hCross with ⟨t, ht⟩
  have htPos : 0 < t := by
    by_contra ht0
    have htEq : t = 0 := by
      omega
    subst t
    simp only [pow_zero, mul_one] at ht
    have hleft := S.left_below
    unfold CriticalPowerFraction.Below at hleft
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hleft)) ht
  refine ⟨t, by omega, ?_⟩
  unfold Above
  dsimp [combine]
  rw [pow_add, pow_add]
  have h2 : 2 ^ (t * S.right.q) = (2 ^ S.right.q) ^ t := by
    rw [Nat.mul_comm, pow_mul]
  have h3 : 3 ^ (t * S.right.p) = (3 ^ S.right.p) ^ t := by
    rw [Nat.mul_comm, pow_mul]
  rw [h2, h3]
  exact ht

private theorem exists_below_combine_of_above_below
    (S : CriticalAboveBelowState) :
    ∃ t : ℕ, 1 ≤ t ∧ (combine S.left S.right t).Below := by
  have hCross :=
    exists_pow_ratio_cross
      (A := 3 ^ S.left.p)
      (B := 2 ^ S.left.q)
      (C := 2 ^ S.right.q)
      (D := 3 ^ S.right.p)
      (by positivity) (by positivity) (by positivity) (by positivity) S.right_below
  rcases hCross with ⟨t, ht⟩
  have htPos : 0 < t := by
    by_contra ht0
    have htEq : t = 0 := by
      omega
    subst t
    simp only [pow_zero, mul_one] at ht
    have hleft := S.left_above
    change 2 ^ S.left.q < 3 ^ S.left.p at hleft
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hleft)) ht
  refine ⟨t, by omega, ?_⟩
  unfold Below
  dsimp [combine]
  rw [pow_add, pow_add]
  have h3 : 3 ^ (t * S.right.p) = (3 ^ S.right.p) ^ t := by
    rw [Nat.mul_comm, pow_mul]
  have h2 : 2 ^ (t * S.right.q) = (2 ^ S.right.q) ^ t := by
    rw [Nat.mul_comm, pow_mul]
  rw [h3, h2]
  exact ht

def belowAboveFlipTime
    (S : CriticalBelowAboveState) : ℕ :=
  Nat.find (exists_above_combine_of_below_above S)

def aboveBelowFlipTime
    (S : CriticalAboveBelowState) : ℕ :=
  Nat.find (exists_below_combine_of_above_below S)

def belowAboveMultiplier
    (S : CriticalBelowAboveState) : ℕ :=
  belowAboveFlipTime S - 1

def aboveBelowMultiplier
    (S : CriticalAboveBelowState) : ℕ :=
  aboveBelowFlipTime S - 1

private theorem belowAboveFlipTime_ge_two
    (S : CriticalBelowAboveState) :
    2 ≤ belowAboveFlipTime S := by
  have hs :
      1 ≤ belowAboveFlipTime S ∧
        (combine S.left S.right (belowAboveFlipTime S)).Above := by
    simpa [belowAboveFlipTime] using
      Nat.find_spec (exists_above_combine_of_below_above S)
  have hpos := hs.1
  by_contra hnot
  have heq : belowAboveFlipTime S = 1 := by
    omega
  have habove := hs.2
  rw [heq] at habove
  have hbelow := S.mediant_left
  unfold CriticalPowerFraction.Below at hbelow
  unfold CriticalPowerFraction.Above at habove
  omega

private theorem aboveBelowFlipTime_ge_two
    (S : CriticalAboveBelowState) :
    2 ≤ aboveBelowFlipTime S := by
  have hs :
      1 ≤ aboveBelowFlipTime S ∧
        (combine S.left S.right (aboveBelowFlipTime S)).Below := by
    simpa [aboveBelowFlipTime] using
      Nat.find_spec (exists_below_combine_of_above_below S)
  have hpos := hs.1
  by_contra hnot
  have heq : aboveBelowFlipTime S = 1 := by
    omega
  have hbelow := hs.2
  rw [heq] at hbelow
  have habove := S.mediant_left
  unfold CriticalPowerFraction.Below at hbelow
  unfold CriticalPowerFraction.Above at habove
  omega

private theorem belowAboveMultiplier_pos
    (S : CriticalBelowAboveState) :
    0 < belowAboveMultiplier S := by
  unfold belowAboveMultiplier
  have := belowAboveFlipTime_ge_two S
  omega

private theorem aboveBelowMultiplier_pos
    (S : CriticalAboveBelowState) :
    0 < aboveBelowMultiplier S := by
  unfold aboveBelowMultiplier
  have := aboveBelowFlipTime_ge_two S
  omega

private theorem belowAbove_stays_left
    (S : CriticalBelowAboveState) :
    (combine S.left S.right (belowAboveMultiplier S)).Below := by
  let k := belowAboveMultiplier S
  have hk : 0 < k := by
    simpa [k] using belowAboveMultiplier_pos S
  have hrightp : 0 < S.right.p := by
    by_contra h
    have hp0 : S.right.p = 0 := by
      omega
    have habove := S.right_above
    unfold CriticalPowerFraction.Above at habove
    rw [hp0] at habove
    simp at habove
  rcases CriticalPowerFraction.below_or_above_of_pos
      (combine S.left S.right k) with h | h
  · exact h
  · have hspec :
        1 ≤ k ∧ (combine S.left S.right k).Above :=
      ⟨by omega, h⟩
    have hmin :
        belowAboveFlipTime S ≤ k := by
      simpa [belowAboveFlipTime] using
        Nat.find_min'
          (exists_above_combine_of_below_above S)
          hspec
    have hkEq :
        k = belowAboveFlipTime S - 1 := by
      rfl
    have hflip :
        2 ≤ belowAboveFlipTime S :=
      belowAboveFlipTime_ge_two S
    omega

private theorem aboveBelow_stays_left
    (S : CriticalAboveBelowState) :
    (combine S.left S.right (aboveBelowMultiplier S)).Above := by
  let k := aboveBelowMultiplier S
  have hk : 0 < k := by
    simpa [k] using aboveBelowMultiplier_pos S
  have hleftp : 0 < S.left.p := by
    by_contra h
    have hp0 : S.left.p = 0 := by
      omega
    have habove := S.left_above
    unfold CriticalPowerFraction.Above at habove
    rw [hp0] at habove
    simp at habove
  rcases CriticalPowerFraction.below_or_above_of_pos
      (combine S.left S.right k) with h | h
  · have hspec :
        1 ≤ k ∧ (combine S.left S.right k).Below :=
      ⟨by omega, h⟩
    have hmin :
        aboveBelowFlipTime S ≤ k := by
      simpa [aboveBelowFlipTime] using
        Nat.find_min'
          (exists_below_combine_of_above_below S)
          hspec
    have hkEq :
        k = aboveBelowFlipTime S - 1 := by
      dsimp [k, aboveBelowMultiplier]
    have hflip :
        2 ≤ aboveBelowFlipTime S :=
      aboveBelowFlipTime_ge_two S
    omega
  · exact h

def CriticalBelowAboveState.step
    (S : CriticalBelowAboveState) :
    CriticalAboveBelowState := by
  let k := belowAboveMultiplier S
  let next := combine S.left S.right k
  have hk : 0 < k := by
    simpa [k] using belowAboveMultiplier_pos S
  have hnextBelow : next.Below := by
    simpa [next, k] using belowAbove_stays_left S
  have hflip :
      (combine S.left S.right (belowAboveFlipTime S)).Above := by
    simpa [belowAboveFlipTime] using
      (Nat.find_spec (exists_above_combine_of_below_above S)).2
  have hsucc : k + 1 = belowAboveFlipTime S := by
    dsimp [k, belowAboveMultiplier]
    have hge : 2 ≤ belowAboveFlipTime S :=
      belowAboveFlipTime_ge_two S
    omega
  have hmedEq :
      combine S.right next 1 =
        combine S.left S.right (k + 1) := by
    apply CriticalPowerFraction.ext <;>
      dsimp [next, CriticalPowerFraction.combine] <;>
      ring
  exact {
    left := S.right
    right := next

    left_above := S.right_above
    right_below := hnextBelow

    adjacent :=
      CriticalPowerFraction.fareyAdjacent_right_combine
        S.adjacent k

    mediant_left := by
      rw [hmedEq, hsucc]
      exact hflip

    left_p_pos := S.right_p_pos

    right_p_pos := by
      dsimp [next, CriticalPowerFraction.combine]
      have hprod : 0 < k * S.right.p :=
        Nat.mul_pos hk S.right_p_pos
      omega

    left_p_le_q := S.right_p_le_q

    right_p_le_q := by
      dsimp [next]
      exact
        CriticalPowerFraction.combine_p_le_q
          S.left_p_le_q S.right_p_le_q k

    q_strict := by
      dsimp [next, CriticalPowerFraction.combine]
      have hlq : 0 < S.left.q := S.left.q_pos
      have hrq : 0 < S.right.q := S.right.q_pos
      nlinarith
  }

open CriticalPowerFraction

def CriticalAboveBelowState.step
    (S : CriticalAboveBelowState) :
    CriticalBelowAboveState := by
  let k := aboveBelowMultiplier S
  let next := combine S.left S.right k
  have hk : 0 < k := by
    simpa [k] using aboveBelowMultiplier_pos S
  have hnextAbove : next.Above := by
    simpa [next, k] using aboveBelow_stays_left S
  have hflip :
      (combine S.left S.right (aboveBelowFlipTime S)).Below := by
    simpa [aboveBelowFlipTime] using
      (Nat.find_spec (exists_below_combine_of_above_below S)).2
  have hsucc : k + 1 = aboveBelowFlipTime S := by
    dsimp [k, aboveBelowMultiplier]
    have hge : 2 ≤ aboveBelowFlipTime S :=
      aboveBelowFlipTime_ge_two S
    omega
  have hmedEq :
      combine S.right next 1 =
        combine S.left S.right (k + 1) := by
    apply CriticalPowerFraction.ext <;>
      dsimp [next, CriticalPowerFraction.combine] <;>
      ring
  exact {
    left := S.right
    right := next

    left_below := S.right_below
    right_above := hnextAbove

    adjacent :=
      CriticalPowerFraction.fareyAdjacent_right_combine
        S.adjacent k

    mediant_left := by
      rw [hmedEq, hsucc]
      exact hflip

    left_p_pos := S.right_p_pos

    right_p_pos := by
      dsimp [next, CriticalPowerFraction.combine]
      have hprod : 0 < k * S.right.p :=
        Nat.mul_pos hk S.right_p_pos
      omega

    left_p_le_q := S.right_p_le_q

    right_p_le_q := by
      dsimp [next]
      exact
        CriticalPowerFraction.combine_p_le_q
          S.left_p_le_q S.right_p_le_q k

    q_strict := by
      dsimp [next, CriticalPowerFraction.combine]
      have hl : 0 < S.left.q := S.left.q_pos
      have hr : 0 < S.right.q := S.right.q_pos
      nlinarith
  }
/-- index 12 の convergent `79335/125743`。 -/
def criticalConv12 : CriticalPowerFraction := {
  p := 79335
  q := 125743
  q_pos := by norm_num
}

/-- index 13 の convergent `111202/176251`。 -/
def criticalConv13 : CriticalPowerFraction := {
  p := 111202
  q := 176251
  q_pos := by norm_num
}

/-- tail recursion の初期 Farey pair `(C_12,C_13)`。 -/
def criticalTailStart : CriticalBelowAboveState := {
  left := criticalConv12
  right := criticalConv13
  left_below := by native_decide
  right_above := by native_decide
  adjacent := by
    left
    norm_num [criticalConv12, criticalConv13]
  mediant_left := by native_decide
  left_p_pos := by norm_num [criticalConv12]
  right_p_pos := by norm_num [criticalConv13]
  left_p_le_q := by norm_num [criticalConv12]
  right_p_le_q := by norm_num [criticalConv13]
  q_strict := by norm_num [criticalConv12, criticalConv13]
}

/-- two convergents ずつ tail を進める。 -/
def criticalTailState : ℕ → CriticalBelowAboveState
  | 0 => criticalTailStart
  | n + 1 => (criticalTailState n).step.step

@[simp] theorem criticalTailState_zero :
    criticalTailState 0 = criticalTailStart := rfl

@[simp] theorem criticalTailState_succ (n : ℕ) :
    criticalTailState (n + 1) =
      (criticalTailState n).step.step := rfl

/-- 最初の 12 個の convergent を exact table として持つ。 -/
def criticalInitialConvergent (i : Fin 12) : CriticalPowerFraction :=
  match i.1 with
  | 0 => ⟨0, 1, by norm_num⟩
  | 1 => ⟨1, 1, by norm_num⟩
  | 2 => ⟨1, 2, by norm_num⟩
  | 3 => ⟨2, 3, by norm_num⟩
  | 4 => ⟨5, 8, by norm_num⟩
  | 5 => ⟨12, 19, by norm_num⟩
  | 6 => ⟨41, 65, by norm_num⟩
  | 7 => ⟨53, 84, by norm_num⟩
  | 8 => ⟨306, 485, by norm_num⟩
  | 9 => ⟨665, 1054, by norm_num⟩
  | 10 => ⟨15601, 24727, by norm_num⟩
  | 11 => ⟨31867, 50508, by norm_num⟩
  | _ => ⟨0, 1, by norm_num⟩

/-- actual critical convergent sequence。index 12 以降は exact Farey recursion。 -/
def criticalPowerConvergent (j : ℕ) : CriticalPowerFraction := by
  by_cases hj : j < 12
  · exact criticalInitialConvergent ⟨j, hj⟩
  · let n := j - 12
    let S := criticalTailState (n / 2)
    if hEven : n % 2 = 0 then
      exact S.left
    else
      exact S.right

private theorem criticalTail_even_value (n : ℕ) :
    criticalPowerConvergent (12 + 2 * n) =
      (criticalTailState n).left := by
  simp [criticalPowerConvergent]

private theorem criticalTail_odd_value (n : ℕ) :
    criticalPowerConvergent (13 + 2 * n) =
      (criticalTailState n).right := by
  have h : 13 + 2 * n - 12 = 2 * n + 1 := by
    omega
  have hnot : ¬ 13 + 2 * n < 12 := by
    omega
  have hdiv : (2 * n + 1) / 2 = n := by
    omega
  simp [criticalPowerConvergent, h, hnot, hdiv]


/-- tail の次 even convergent は intermediate above/below step の right。 -/
private theorem criticalTail_next_even
    (n : ℕ) :
    (criticalTailState (n + 1)).left =
      (criticalTailState n).step.right := by
  rfl

/-- exact p sequence。 -/
def criticalPowerP (j : ℕ) : ℕ :=
  (criticalPowerConvergent j).p

/-- exact q sequence。 -/
def criticalPowerQ (j : ℕ) : ℕ :=
  (criticalPowerConvergent j).q

/-- first finite table values。 -/
theorem criticalPowerQ_eight : criticalPowerQ 8 = 485 := by
  norm_num [criticalPowerQ, criticalPowerConvergent, criticalInitialConvergent]

theorem criticalPowerQ_nine : criticalPowerQ 9 = 1054 := by
  norm_num [criticalPowerQ, criticalPowerConvergent, criticalInitialConvergent]

theorem criticalPowerQ_eleven : criticalPowerQ 11 = 50508 := by
  norm_num [criticalPowerQ, criticalPowerConvergent, criticalInitialConvergent]

theorem criticalPowerP_eight : criticalPowerP 8 = 306 := by
  norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent]

theorem criticalPowerP_nine : criticalPowerP 9 = 665 := by
  norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent]

/-- tail even indices are below。 -/
theorem criticalPowerConvergent_below_even_tail
    (n : ℕ) :
    (criticalPowerConvergent (12 + 2 * n)).Below := by
  rw [criticalTail_even_value]
  exact (criticalTailState n).left_below

/-- tail odd indices are above。 -/
theorem criticalPowerConvergent_above_odd_tail
    (n : ℕ) :
    (criticalPowerConvergent (13 + 2 * n)).Above := by
  rw [criticalTail_odd_value]
  exact (criticalTailState n).right_above

/-- tail consecutive convergents are Farey adjacent。 -/
theorem criticalPowerConvergent_adjacent_tail_even
    (n : ℕ) :
    FareyAdjacent
      (criticalPowerConvergent (12 + 2 * n))
      (criticalPowerConvergent (13 + 2 * n)) := by
  rw [criticalTail_even_value, criticalTail_odd_value]
  exact (criticalTailState n).adjacent

/-- odd-to-next-even pair is Farey adjacent。 -/
theorem criticalPowerConvergent_adjacent_tail_odd
    (n : ℕ) :
    FareyAdjacent
      (criticalPowerConvergent (13 + 2 * n))
      (criticalPowerConvergent (14 + 2 * n)) := by
  rw [criticalTail_odd_value]
  have h14 : 14 + 2 * n = 12 + 2 * (n + 1) := by omega
  rw [h14, criticalTail_even_value, criticalTail_next_even]
  exact (criticalTailState n).step.adjacent

/-- tail denominator is strictly increasing at even-to-odd step。 -/
theorem criticalPowerQ_lt_tail_even (n : ℕ) :
    criticalPowerQ (12 + 2 * n) <
      criticalPowerQ (13 + 2 * n) := by
  unfold criticalPowerQ
  rw [criticalTail_even_value, criticalTail_odd_value]
  exact (criticalTailState n).q_strict

/-- tail denominator is strictly increasing at odd-to-even step。 -/
theorem criticalPowerQ_lt_tail_odd (n : ℕ) :
    criticalPowerQ (13 + 2 * n) <
      criticalPowerQ (14 + 2 * n) := by
  unfold criticalPowerQ
  rw [criticalTail_odd_value]
  have h14 : 14 + 2 * n = 12 + 2 * (n + 1) := by omega
  rw [h14, criticalTail_even_value, criticalTail_next_even]
  exact (criticalTailState n).step.q_strict

/-- initial table の power orientation は exact computation で確認する。 -/
theorem criticalInitial_orientation
    (j : ℕ)
    (hj : j < 12) :
    (j % 2 = 0 → (criticalPowerConvergent j).Below) ∧
    (j % 2 = 1 → (criticalPowerConvergent j).Above) := by
  interval_cases j <;>
    simp only [Nat.zero_mod, Below, criticalPowerConvergent, Nat.ofNat_pos, ↓reduceDIte,
     criticalInitialConvergent,pow_zero, pow_one, Order.lt_two_iff, Std.le_refl, imp_self,
      zero_ne_one, Above, Nat.not_ofNat_lt_one, and_self] <;>
    native_decide

/-- actual convergent の global parity orientation。 -/
theorem criticalPower_orientation
    (j : ℕ) :
    (j % 2 = 0 → (criticalPowerConvergent j).Below) ∧
    (j % 2 = 1 → (criticalPowerConvergent j).Above) := by
  by_cases hj : j < 12
  · exact criticalInitial_orientation j hj
  · have hj12 : 12 ≤ j := by omega
    have hrepr :
        (∃ n, j = 12 + 2 * n) ∨
        (∃ n, j = 13 + 2 * n) := by
      let n := (j - 12) / 2
      have hmod : (j - 12) % 2 = 0 ∨ (j - 12) % 2 = 1 := by
        have hlt := Nat.mod_lt (j - 12) (by decide : 0 < 2)
        omega
      rcases hmod with h | h
      · left
        refine ⟨n, ?_⟩
        dsimp [n]
        have hdiv := Nat.mod_add_div (j - 12) 2
        omega
      · right
        refine ⟨n, ?_⟩
        dsimp [n]
        have hdiv := Nat.mod_add_div (j - 12) 2
        omega
    rcases hrepr with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · constructor
      · intro _
        exact criticalPowerConvergent_below_even_tail n
      · intro h
        have : (12 + 2 * n) % 2 = 0 := by omega
        omega
    · constructor
      · intro h
        have : (13 + 2 * n) % 2 = 1 := by omega
        omega
      · intro _
        exact criticalPowerConvergent_above_odd_tail n

/-- all actual denominators are positive。 -/
theorem criticalPowerQ_pos (j : ℕ) : 0 < criticalPowerQ j :=
  (criticalPowerConvergent j).q_pos

/-- actual numerator is positive from index 1 onward。 -/
theorem criticalPowerP_pos
    {j : ℕ}
    (hj : 1 ≤ j) :
    0 < criticalPowerP j := by
  by_cases hsmall : j < 12
  · interval_cases j <;>
      norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent] at *
  · have hj12 : 12 ≤ j := by omega
    have hrepr :
        (∃ n, j = 12 + 2 * n) ∨
        (∃ n, j = 13 + 2 * n) := by
      let n := (j - 12) / 2
      have hlt := Nat.mod_lt (j - 12) (by decide : 0 < 2)
      have hdiv := Nat.mod_add_div (j - 12) 2
      by_cases h : (j - 12) % 2 = 0
      · left; refine ⟨n, by dsimp [n]; omega⟩
      · right; refine ⟨n, by dsimp [n]; omega⟩
    rcases hrepr with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · unfold criticalPowerP
      rw [criticalTail_even_value]
      exact (criticalTailState n).left_p_pos
    · unfold criticalPowerP
      rw [criticalTail_odd_value]
      exact (criticalTailState n).right_p_pos

/-- all actual convergents stay in `[0,1]`。 -/
theorem criticalPowerP_le_Q (j : ℕ) :
    criticalPowerP j ≤ criticalPowerQ j := by
  by_cases hsmall : j < 12
  · interval_cases j <;>
      norm_num [criticalPowerP, criticalPowerQ,
        criticalPowerConvergent, criticalInitialConvergent] at *
  · have hj12 : 12 ≤ j := by
      omega
    let n := (j - 12) / 2
    have hlt := Nat.mod_lt (j - 12) (by decide : 0 < 2)
    have hdiv := Nat.mod_add_div (j - 12) 2
    by_cases h : (j - 12) % 2 = 0
    · have hjEq : j = 12 + 2 * n := by
        dsimp [n]
        omega
      rw [hjEq]
      unfold criticalPowerP criticalPowerQ
      rw [criticalTail_even_value]
      exact (criticalTailState n).left_p_le_q
    · have hmod1 : (j - 12) % 2 = 1 := by
        omega
      have hjEq : j = 13 + 2 * n := by
        dsimp [n]
        omega
      rw [hjEq]
      unfold criticalPowerP criticalPowerQ
      rw [criticalTail_odd_value]
      exact (criticalTailState n).right_p_le_q

/-- global denominator monotonicity。 -/
theorem criticalPowerQ_mono (j : ℕ) :
    criticalPowerQ j ≤ criticalPowerQ (j + 1) := by
  by_cases hsmall : j < 12
  · interval_cases j <;>
      norm_num [criticalPowerQ, criticalPowerConvergent,
        criticalInitialConvergent, criticalConv12, criticalTailStart,
        criticalTailState] at *
  · have hj12 : 12 ≤ j := by omega
    let n := (j - 12) / 2
    have hlt := Nat.mod_lt (j - 12) (by decide : 0 < 2)
    have hdiv := Nat.mod_add_div (j - 12) 2
    by_cases h : (j - 12) % 2 = 0
    · have hjEq : j = 12 + 2 * n := by dsimp [n]; omega
      rw [hjEq]
      simpa [show 12 + 2 * n + 1 = 13 + 2 * n by omega] using
        (le_of_lt (criticalPowerQ_lt_tail_even n))
    · have hmod1 : (j - 12) % 2 = 1 := by omega
      have hjEq : j = 13 + 2 * n := by dsimp [n]; omega
      rw [hjEq]
      simpa [show 13 + 2 * n + 1 = 14 + 2 * n by omega] using
        (le_of_lt (criticalPowerQ_lt_tail_odd n))

/-- initial range `1 ≤ i < 12` では denominator は次へ strict に増える。 -/
private theorem criticalPowerQ_strict_succ_initial
    {i : ℕ}
    (hi : 1 ≤ i)
    (hsmall : i < 12) :
    criticalPowerQ i < criticalPowerQ (i + 1) := by
  interval_cases i <;>
    norm_num [criticalPowerQ, criticalPowerConvergent,
      criticalInitialConvergent, criticalConv12, criticalTailStart,
      criticalTailState] at *


/-- tail range `12 ≤ i` では denominator は次へ strict に増える。 -/
private theorem criticalPowerQ_strict_succ_tail
    {i : ℕ}
    (hi12 : 12 ≤ i) :
    criticalPowerQ i < criticalPowerQ (i + 1) := by
  let n := (i - 12) / 2
  have hlt := Nat.mod_lt (i - 12) (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div (i - 12) 2
  by_cases h : (i - 12) % 2 = 0
  · have hiEq : i = 12 + 2 * n := by
      dsimp [n]
      omega
    rw [hiEq]
    have hsucc : 12 + 2 * n + 1 = 13 + 2 * n := by
      omega
    rw [hsucc]
    exact criticalPowerQ_lt_tail_even n
  · have hmod1 : (i - 12) % 2 = 1 := by
      omega
    have hiEq : i = 13 + 2 * n := by
      dsimp [n]
      omega
    rw [hiEq]
    have hsucc : 13 + 2 * n + 1 = 14 + 2 * n := by
      omega
    rw [hsucc]
    exact criticalPowerQ_lt_tail_odd n


/-- index 1 以降 denominator は successor に対して strict に増える。 -/
private theorem criticalPowerQ_strict_succ
    {i : ℕ}
    (hi : 1 ≤ i) :
    criticalPowerQ i < criticalPowerQ (i + 1) := by
  by_cases hsmall : i < 12
  · exact criticalPowerQ_strict_succ_initial hi hsmall
  · have hi12 : 12 ≤ i := by
      omega
    exact criticalPowerQ_strict_succ_tail hi12


/-- index 2 以降 denominator は strict に増える。 -/
theorem criticalPowerQ_strict_previous
    {j : ℕ}
    (hj : 2 ≤ j) :
    criticalPowerQ (j - 1) < criticalPowerQ j := by
  have hi : 1 ≤ j - 1 := by
    omega
  have hstep :=
    criticalPowerQ_strict_succ (i := j - 1) hi
  have hjEq : (j - 1) + 1 = j := by
    omega
  simpa [hjEq] using hstep

/-- denominator sequence is cofinal。 -/
theorem criticalPowerQ_cofinal :
    ∀ N : ℕ, ∃ j : ℕ,
      9 ≤ j ∧ N ≤ criticalPowerQ j := by
  intro N
  refine ⟨12 + N, by omega, ?_⟩
  have hbase : 12 + N ≤ criticalPowerQ (12 + N) := by
    induction N with
    | zero =>
        norm_num [criticalPowerQ, criticalPowerConvergent,
          criticalConv12, criticalTailState, criticalTailStart]
    | succ n ih =>
        have hs := criticalPowerQ_strict_previous
          (j := 12 + (n + 1)) (by omega)
        have hs' :
            criticalPowerQ (12 + n) <
              criticalPowerQ (12 + (n + 1)) := by
          simpa only [
            show 12 + (n + 1) - 1 = 12 + n by omega
          ] using hs
        have hstep :
            criticalPowerQ (12 + n) + 1 ≤
              criticalPowerQ (12 + (n + 1)) := by
          exact Nat.succ_le_of_lt hs'
        omega
  omega

/-- actual power-Farey sequence as existing strong-route CF interface。 -/
def actualCriticalContinuedFractionData :
    CriticalContinuedFractionData := {
  p := criticalPowerP
  q := criticalPowerQ
  start := 9
  start_ge_three := by norm_num
  p_pos := by
    intro j hj
    exact criticalPowerP_pos (by omega)
  q_pos := by
    intro j _
    exact criticalPowerQ_pos j
  q_mono := criticalPowerQ_mono
  q_strict_previous := by
    intro j hj
    exact criticalPowerQ_strict_previous (by omega)
  q_cofinal := criticalPowerQ_cofinal
}

/-- parity orientation included, with no external theorem。 -/
def actualOrientedCriticalContinuedFractionData :
    OrientedCriticalContinuedFractionData := {
  base := actualCriticalContinuedFractionData
  q_pos_all := criticalPowerQ_pos
  odd_p_pos := by
    intro j hjOdd
    have hj : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      subst j
      norm_num at hjOdd
    exact criticalPowerP_pos hj
  odd_above := by
    intro j hj
    exact (criticalPower_orientation j).2 hj
  even_below := by
    intro j hj
    exact (criticalPower_orientation j).1 hj
}

@[simp] theorem actualCritical_start :
    actualCriticalContinuedFractionData.start = 9 := rfl

@[simp] theorem actualCritical_q_eight :
    actualCriticalContinuedFractionData.q 8 = 485 :=
  criticalPowerQ_eight

@[simp] theorem actualCritical_q_nine :
    actualCriticalContinuedFractionData.q 9 = 1054 :=
  criticalPowerQ_nine


/-- initial range `9 ≤ j < 12` では consecutive convergents は Farey adjacent。 -/
private theorem criticalPower_adjacent_next_initial
    {j : ℕ}
    (hj9 : 9 ≤ j)
    (hj12 : j < 12) :
    CriticalPowerFraction.FareyAdjacent
      (criticalPowerConvergent j)
      (criticalPowerConvergent (j + 1)) := by
  interval_cases j <;>
    norm_num [criticalPowerConvergent, criticalInitialConvergent,
      criticalConv12, criticalTailStart,
      CriticalPowerFraction.FareyAdjacent] at *


/-- tail range `12 ≤ j` では consecutive convergents は Farey adjacent。 -/
private theorem criticalPower_adjacent_next_tail
    {j : ℕ}
    (hj12 : 12 ≤ j) :
    CriticalPowerFraction.FareyAdjacent
      (criticalPowerConvergent j)
      (criticalPowerConvergent (j + 1)) := by
  let n := (j - 12) / 2
  have hlt := Nat.mod_lt (j - 12) (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div (j - 12) 2
  by_cases h : (j - 12) % 2 = 0
  · have hjEq : j = 12 + 2 * n := by
      dsimp [n]
      omega
    have hnext : j + 1 = 13 + 2 * n := by
      omega
    rw [hnext, hjEq]
    exact criticalPowerConvergent_adjacent_tail_even n
  · have hmod1 : (j - 12) % 2 = 1 := by
      omega
    have hjEq : j = 13 + 2 * n := by
      dsimp [n]
      omega
    have hnext : j + 1 = 14 + 2 * n := by
      omega
    rw [hnext, hjEq]
    exact criticalPowerConvergent_adjacent_tail_odd n


/-- start=9 以降の consecutive actual convergents は Farey adjacent。 -/
theorem criticalPower_adjacent_next
    {j : ℕ}
    (hj : 9 ≤ j) :
    CriticalPowerFraction.FareyAdjacent
      (criticalPowerConvergent j)
      (criticalPowerConvergent (j + 1)) := by
  by_cases hj12 : j < 12
  · exact criticalPower_adjacent_next_initial hj hj12
  · have hbase : 12 ≤ j := by
      omega
    exact criticalPower_adjacent_next_tail hbase

/-- start=9 以降の current/next は critical slope の反対側にある。 -/
theorem criticalPower_opposite_next
    {j : ℕ} :
    ((j % 2 = 0 ∧
        (criticalPowerConvergent j).Below ∧
        (criticalPowerConvergent (j + 1)).Above) ∨
      (j % 2 = 1 ∧
        (criticalPowerConvergent j).Above ∧
        (criticalPowerConvergent (j + 1)).Below)) := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by
    have hlt := Nat.mod_lt j (by decide : 0 < 2)
    omega
  rcases hmod with hEven | hOdd
  · left
    refine ⟨hEven, (criticalPower_orientation j).1 hEven, ?_⟩
    have hnextOdd : (j + 1) % 2 = 1 := by omega
    exact (criticalPower_orientation (j + 1)).2 hnextOdd
  · right
    refine ⟨hOdd, (criticalPower_orientation j).2 hOdd, ?_⟩
    have hnextEven : (j + 1) % 2 = 0 := by omega
    exact (criticalPower_orientation (j + 1)).1 hnextEven

/-- start=9 以降 next denominator は current より真に大きい。 -/
theorem criticalPowerQ_lt_next
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalPowerQ j < criticalPowerQ (j + 1) := by
  exact criticalPowerQ_strict_previous (j := j + 1) (by omega)



/-- denominator monotonicity on arbitrary indices。 -/
theorem criticalPowerQ_mono_of_le
    {a b : ℕ}
    (h : a ≤ b) :
    criticalPowerQ a ≤ criticalPowerQ b := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases hab : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact le_trans (ih hab') (criticalPowerQ_mono b)


/-- index 8 からの adjacency。start=9 の previous/current roof 証明で使う。 -/
theorem criticalPower_adjacent_next_from_eight
    {j : ℕ}
    (hj : 8 ≤ j) :
    CriticalPowerFraction.FareyAdjacent
      (criticalPowerConvergent j)
      (criticalPowerConvergent (j + 1)) := by
  by_cases h9 : 9 ≤ j
  · exact criticalPower_adjacent_next h9
  · have hj8 : j = 8 := by omega
    subst j
    norm_num [criticalPowerConvergent, criticalInitialConvergent,
      CriticalPowerFraction.FareyAdjacent]

end ExternalArithmetic
end CSTMicro
end Collatz2
