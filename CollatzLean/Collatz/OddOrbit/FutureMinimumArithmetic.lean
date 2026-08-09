import CollatzLean.Collatz.OddOrbit.FutureMinimum
import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# future minimumの一段算術

非有界odd-only軌道のfuture minimumでは開始指数はexactに1。
そこから`value+1`の4整除性と隣接値差の4整除性を得る。
-/

namespace Collatz
namespace OddOrbit

/-- 非有界軌道のfuture minimumではactual exponentはexactに1。 -/
theorem FutureMinimumAt.exponent_eq_one
    {O : OddOrbit} {n : ℕ} (hmin : O.FutureMinimumAt n) (hU : O.Unbounded) :
    O.exponent n = 1 := by
  have hePos := O.exponent_pos n
  by_contra hne
  have heTwo : 2 ≤ O.exponent n := by omega
  have hpow : 4 ≤ 2 ^ O.exponent n := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
  have hstep := O.step n
  have hstartPos := O.value_pos n
  have hscaled : 4 * O.value (n + 1) ≤ 4 * O.value n := by
    calc
      4 * O.value (n + 1)
          ≤ 2 ^ O.exponent n * O.value (n + 1) :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value n + 1 := hstep
      _ ≤ 4 * O.value n := by omega
  have hnextLe : O.value (n + 1) ≤ O.value n :=
    Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hstartLe : O.value n ≤ O.value (n + 1) := hmin _ (by omega)
  have heq : O.value n = O.value (n + 1) := Nat.le_antisymm hstartLe hnextLe
  exact (O.value_ne_of_lt_of_unbounded hU (by omega : n < n + 1)) heq

/-- future minimumでは`value+1`が4で割り切れる。 -/
theorem FutureMinimumAt.four_dvd_value_add_one
    {O : OddOrbit} {n : ℕ} (hmin : O.FutureMinimumAt n) (hU : O.Unbounded) :
    ∃ q : ℕ, O.value n + 1 = 4 * q := by
  have he : O.exponent n = 1 := hmin.exponent_eq_one hU
  have hs : 2 * O.value (n + 1) = 3 * O.value n + 1 := by
    simpa [he] using O.step n
  rcases O.value_odd n with ⟨a, ha⟩
  rcases O.value_odd (n + 1) with ⟨b, hb⟩
  rw [ha, hb] at hs
  obtain ⟨k, hEven | hOdd⟩ := a.even_or_odd'
  · rw [hEven] at hs
    omega
  · refine ⟨k + 1, ?_⟩
    rw [ha, hOdd]
    ring

/-- future minimumの`value+1` exact depthは2以上。 -/
theorem FutureMinimumAt.value_add_one_depth_two_le
    {O : OddOrbit} {n : ℕ} (hmin : O.FutureMinimumAt n) (hU : O.Unbounded)
    {A u : ℕ}
    (hA : TwoAdic.ExactFactor (O.value n + 1) A u) :
    2 ≤ A := by
  obtain ⟨q, hq⟩ := hmin.four_dvd_value_add_one hU
  by_contra hnot
  have hcases : A = 0 ∨ A = 1 := by omega
  rcases hcases with rfl | rfl
  · rcases hA with ⟨hfac, hodd⟩
    simp only [pow_zero, one_mul] at hfac
    have huEq : u = 4 * q := by omega
    have huEven : Even u := by
      rw [huEq]
      exact ⟨2 * q, by ring⟩
    exact TwoAdic.odd_even_false hodd huEven
  · rcases hA with ⟨hfac, hodd⟩
    norm_num at hfac
    have huEven : Even u := by
      refine ⟨q, ?_⟩
      omega
    exact TwoAdic.odd_even_false hodd huEven

/-- exponent=1の二位置で値が増えるなら値差は4の倍数。 -/
theorem four_dvd_value_gap_of_exponent_one
    (O : OddOrbit) {i j : ℕ}
    (hij : O.value i < O.value j)
    (hei : O.exponent i = 1)
    (hej : O.exponent j = 1) :
    ∃ q : ℕ, O.value j - O.value i = 4 * q := by
  have hsi : 2 * O.value (i + 1) = 3 * O.value i + 1 := by
    simpa [hei] using O.step i
  have hsj : 2 * O.value (j + 1) = 3 * O.value j + 1 := by
    simpa [hej] using O.step j
  rcases O.value_odd (i + 1) with ⟨a, ha⟩
  rcases O.value_odd (j + 1) with ⟨b, hb⟩
  rw [ha] at hsi
  rw [hb] at hsj
  have hab : a < b := by omega
  let d := O.value j - O.value i
  let t := b - a
  have hrelation : 3 * d = 4 * t := by
    dsimp [d, t]
    omega
  have htd : t < d := by
    dsimp [d, t]
    omega
  refine ⟨d - t, ?_⟩
  dsimp [d, t] at hrelation htd ⊢
  omega

end OddOrbit
end Collatz
