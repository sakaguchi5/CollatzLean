import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# 正差の2進depth

二つの正整数の完全2進分解と、その正差の完全2進分解だけから
valuation triangleを得る。Collatz軌道には依存しない。
-/

namespace Collatz
namespace TwoAdic

/-- 左側depthが小さいなら正差のdepthも左側に一致する。 -/
theorem sub_depth_eq_left_of_lt
    {X Y A C u v D t : ℕ}
    (hX : ExactFactor X A u)
    (hY : ExactFactor Y C v)
    (hD : ExactFactor (Y - X) D t)
    (hXY : X < Y)
    (hAC : A < C) :
    D = A := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, C = A + (r + 1) := by
    exact ⟨C - A - 1, by omega⟩
  let V : ℕ := 2 ^ (r + 1) * v
  have hY' : Y = 2 ^ A * V := by
    dsimp [V]
    rw [hY.1, hr, pow_add]
    ring
  have hX' : X = 2 ^ A * u := hX.1
  have hpowPos : 0 < 2 ^ A := Nat.pow_pos (by omega)
  have huV : u < V := by
    have hmul : 2 ^ A * u < 2 ^ A * V := by
      simpa [hX', hY'] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  let q : ℕ := V - u
  have hdiff : Y - X = 2 ^ A * q := by
    dsimp [q]
    rw [hY', hX', Nat.mul_sub_left_distrib]
  have hqOdd : Odd q := by
    rcases hX.2 with ⟨ku, hku⟩
    let T : ℕ := 2 ^ r * v
    have hV : V = 2 * T := by
      dsimp [V, T]
      rw [pow_succ]
      ring
    have hkuT : ku < T := by
      rw [hku, hV] at huV
      omega
    refine ⟨T - ku - 1, ?_⟩
    dsimp [q]
    rw [hku, hV]
    omega
  have hCandidate : ExactFactor (Y - X) A q :=
    ⟨hdiff, hqOdd⟩
  exact exponent_unique hD hCandidate

/-- 右側depthが小さいなら正差のdepthも右側に一致する。 -/
theorem sub_depth_eq_right_of_lt
    {X Y A C u v D t : ℕ}
    (hX : ExactFactor X A u)
    (hY : ExactFactor Y C v)
    (hD : ExactFactor (Y - X) D t)
    (hXY : X < Y)
    (hCA : C < A) :
    D = C := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, A = C + (r + 1) := by
    exact ⟨A - C - 1, by omega⟩
  let U : ℕ := 2 ^ (r + 1) * u
  have hX' : X = 2 ^ C * U := by
    dsimp [U]
    rw [hX.1, hr, pow_add]
    ring
  have hY' : Y = 2 ^ C * v := hY.1
  have hpowPos : 0 < 2 ^ C := Nat.pow_pos (by omega)
  have hUv : U < v := by
    have hmul : 2 ^ C * U < 2 ^ C * v := by
      simpa [hX', hY'] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  let q : ℕ := v - U
  have hdiff : Y - X = 2 ^ C * q := by
    dsimp [q]
    rw [hY', hX', Nat.mul_sub_left_distrib]
  have hqOdd : Odd q := by
    rcases hY.2 with ⟨kv, hkv⟩
    let T : ℕ := 2 ^ r * u
    have hU : U = 2 * T := by
      dsimp [U, T]
      rw [pow_succ]
      ring
    have hTkv : T ≤ kv := by
      rw [hU, hkv] at hUv
      omega
    refine ⟨kv - T, ?_⟩
    dsimp [q]
    rw [hU, hkv]
    omega
  have hCandidate : ExactFactor (Y - X) C q :=
    ⟨hdiff, hqOdd⟩
  exact exponent_unique hD hCandidate

/-- 両側depthが等しいなら正差は少なくとも1bit深い。 -/
theorem depth_lt_sub_depth_of_eq
    {X Y A u v D t : ℕ}
    (hX : ExactFactor X A u)
    (hY : ExactFactor Y A v)
    (hD : ExactFactor (Y - X) D t)
    (hXY : X < Y) :
    A < D := by
  have hpowPos : 0 < 2 ^ A := Nat.pow_pos (by omega)
  have huv : u < v := by
    have hmul : 2 ^ A * u < 2 ^ A * v := by
      simpa [hX.1, hY.1] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  rcases hX.2 with ⟨ku, hku⟩
  rcases hY.2 with ⟨kv, hkv⟩
  have hk : ku < kv := by
    rw [hku, hkv] at huv
    omega
  let q : ℕ := kv - ku
  have hdiffOddParts : v - u = 2 * q := by
    dsimp [q]
    rw [hku, hkv]
    omega
  have hdiff : Y - X = 2 ^ (A + 1) * q := by
    rw [hY.1, hX.1, ← Nat.mul_sub_left_distrib, hdiffOddParts, pow_succ]
    ring
  by_contra hnot
  have hDle : D ≤ A := Nat.le_of_not_gt hnot
  have hDlt : D < A + 1 := by omega
  have hpowEq : 2 ^ D * t = 2 ^ (A + 1) * q := by
    calc
      2 ^ D * t = Y - X := hD.1.symm
      _ = 2 ^ (A + 1) * q := hdiff
  obtain ⟨r, ht⟩ := oddPart_eq_twoPow_mul_of_lt hpowEq hDlt
  have htEven : Even t := by
    rw [ht]
    exact even_two_pow_succ_mul r q
  exact odd_even_false hD.2 htEven

end TwoAdic
end Collatz
