import CollatzLean.Collatz.OddOrbit.Periodic
import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# high exponentの有限局所算術

`exponent > 1`をhigh eventと呼ぶ。
周期指数tailの反復排除から、high eventは任意の位置以後に存在する。
またhigh eventでは`value+1`の2進depthがexactに1であり、
その直前の指数1 runを逆向きに辿るとdepthが1ずつ増える。
-/

namespace Collatz
namespace OddOrbit

/-- 指数が1より真に大きい位置。 -/
def HighExponentAt (O : OddOrbit) (n : ℕ) : Prop :=
  1 < O.exponent n

/-- high eventは任意の位置以後に存在する。 -/
theorem exists_highExponent_at_or_after
    (O : OddOrbit) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ O.HighExponentAt n := by
  by_contra hnone
  have hno : ∀ n : ℕ, N ≤ n → ¬ O.HighExponentAt n := by
    intro n hn hhigh
    exact hnone ⟨n, hn, hhigh⟩
  have hconstant : ∀ n : ℕ, N ≤ n → O.exponent n = 1 := by
    intro n hn
    have hpos := O.exponent_pos n
    have hnotHigh := hno n hn
    unfold HighExponentAt at hnotHigh
    omega
  have hperiod : ∀ t : ℕ,
      O.exponent (N + t + 1) = O.exponent (N + t) := by
    intro t
    rw [hconstant (N + t + 1) (by omega)]
    rw [hconstant (N + t) (by omega)]
  have hword : O.segment N 1 = [1] := by
    simp [hconstant N le_rfl]
  have hExpanding : (O.segment N 1).Expanding := by
    rw [hword]
    norm_num [Word.Expanding, Word.oddSteps, Word.twoSteps]
  exact O.no_expanding_periodic_exponent_tail
    (q := 1) hperiod hExpanding

/-- high eventでは`value+1`の完全2進depthはexactに1。 -/
theorem highExponent_value_add_one_exact_one
    (O : OddOrbit)
    {i : ℕ}
    (hhigh : O.HighExponentAt i) :
    ∃ u : ℕ, TwoAdic.ExactFactor (O.value i + 1) 1 u := by
  rcases O.value_odd i with ⟨a, ha⟩
  obtain ⟨k, haEven | haOdd⟩ := a.even_or_odd'
  · refine ⟨2 * k + 1, ?_⟩
    constructor
    · rw [ha, haEven]
      norm_num
      ring
    · exact ⟨k, by ring⟩
  · have hOne :
        TwoAdic.ExactFactor (3 * O.value i + 1) 1 (6 * k + 5) := by
      constructor
      · rw [ha, haOdd]
        norm_num
        ring
      · exact ⟨3 * k + 2, by ring⟩
    have hActual :
        TwoAdic.ExactFactor
          (3 * O.value i + 1)
          (O.exponent i)
          (O.value (i + 1)) :=
      ⟨(O.step i).symm, O.value_odd (i + 1)⟩
    have heq := TwoAdic.exponent_unique hActual hOne
    unfold HighExponentAt at hhigh
    omega

/-- 指数1の一段を逆向きに見ると`value+1`のdepthはexactに1増える。 -/
theorem value_add_one_exactFactor_prev_of_exponent_one
    (O : OddOrbit)
    {i d u : ℕ}
    (hexp : O.exponent i = 1)
    (hNext : TwoAdic.ExactFactor (O.value (i + 1) + 1) d u) :
    ∃ v : ℕ, TwoAdic.ExactFactor (O.value i + 1) (d + 1) v := by
  obtain ⟨a, v, hCurrent⟩ :=
    TwoAdic.exists_of_pos (O.value i + 1) (by
      have := O.value_pos i
      omega)
  have hThreeCurrent :
      TwoAdic.ExactFactor (3 * (O.value i + 1)) a (3 * v) := by
    constructor
    · rw [hCurrent.1]
      ring
    · exact (show Odd (3 : ℕ) by decide).mul hCurrent.2
  have hstep : 2 * O.value (i + 1) = 3 * O.value i + 1 := by
    simpa [hexp] using O.step i
  have hScaledNext :
      TwoAdic.ExactFactor (3 * (O.value i + 1)) (d + 1) u := by
    constructor
    · calc
        3 * (O.value i + 1)
            = (3 * O.value i + 1) + 2 := by ring
        _ = 2 * O.value (i + 1) + 2 := by rw [← hstep]
        _ = 2 * (O.value (i + 1) + 1) := by ring
        _ = 2 * (2 ^ d * u) := by rw [hNext.1]
        _ = 2 ^ (d + 1) * u := by
          rw [pow_succ]
          ring
    · exact hNext.2
  have ha : a = d + 1 := TwoAdic.exponent_unique hThreeCurrent hScaledNext
  refine ⟨v, ?_⟩
  simpa [ha] using hCurrent

/--
長さ`L`の指数1区間の直後がhigh eventなら、
区間開始値`+1`の2進depthはexactに`L+1`。
-/
theorem value_add_one_exactFactor_of_one_run_to_high
    (O : OddOrbit) :
    ∀ {start L : ℕ},
      (∀ k : ℕ, k < L → O.exponent (start + k) = 1) →
      O.HighExponentAt (start + L) →
      ∃ u : ℕ, TwoAdic.ExactFactor (O.value start + 1) (L + 1) u := by
  intro start L
  induction L generalizing start with
  | zero =>
      intro _ hhigh
      simpa using O.highExponent_value_add_one_exact_one hhigh
  | succ L ih =>
      intro hones hhigh
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail : ∀ k : ℕ, k < L →
          O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hhighTail : O.HighExponentAt (start + 1 + L) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhigh
      obtain ⟨u, hu⟩ := ih (start := start + 1) htail hhighTail
      obtain ⟨v, hv⟩ :=
        O.value_add_one_exactFactor_prev_of_exponent_one hfirst hu
      refine ⟨v, ?_⟩
      simpa [Nat.add_assoc] using hv

end OddOrbit
end Collatz
