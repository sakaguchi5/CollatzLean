import CollatzLean.Collatz2.Geometry.CriticalProfile

/-!
# Collatz2 Geometry: critical-height carry

`criticalHeight` は `k log_2 3` の整数 roof なので、加法に対して carry は高々1。
この 0/1 carry を record block gluing の純算術座標として独立化する。
-/

namespace Collatz2
namespace Word

@[simp] theorem criticalHeight_zero : criticalHeight 0 = 0 := by
  simp [criticalHeight]

/-- critical roof の次の2冪は `3^k` 以上。 -/
theorem threePow_le_twoPow_criticalHeight_succ
    (k : ℕ) :
    3 ^ k ≤ 2 ^ (criticalHeight k + 1) := by
  by_contra hnot
  have hlt : 2 ^ (criticalHeight k + 1) < 3 ^ k := by omega
  have hle := le_criticalHeight_of_twoPow_lt_threePow hlt
  omega

/-- criticalHeight は加法について subadditive defect が非負。 -/
theorem criticalHeight_add_lower
    (a b : ℕ) :
    criticalHeight a + criticalHeight b ≤ criticalHeight (a + b) := by
  by_cases ha0 : a = 0
  · subst a
    simp
  by_cases hb0 : b = 0
  · subst b
    simp
  have haPos : 0 < a := Nat.pos_of_ne_zero ha0
  have hbPos : 0 < b := Nat.pos_of_ne_zero hb0
  have hA := criticalHeight_pow_lt_threePow haPos
  have hB := criticalHeight_pow_lt_threePow hbPos
  have hRightPos : 0 < 2 ^ criticalHeight b := by positivity
  have h1 :
      2 ^ criticalHeight a * 2 ^ criticalHeight b <
        3 ^ a * 2 ^ criticalHeight b :=
    (Nat.mul_lt_mul_right hRightPos).2 hA
  have h2 :
      3 ^ a * 2 ^ criticalHeight b ≤ 3 ^ a * 3 ^ b :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hB)
  have hPow :
      2 ^ (criticalHeight a + criticalHeight b) < 3 ^ (a + b) := by
    calc
      2 ^ (criticalHeight a + criticalHeight b)
          = 2 ^ criticalHeight a * 2 ^ criticalHeight b := by rw [pow_add]
      _ < 3 ^ a * 2 ^ criticalHeight b := h1
      _ ≤ 3 ^ a * 3 ^ b := h2
      _ = 3 ^ (a + b) := by rw [pow_add]
  exact le_criticalHeight_of_twoPow_lt_threePow hPow

/-- criticalHeight の additive excess は高々1。 -/
theorem criticalHeight_add_upper
    (a b : ℕ) :
    criticalHeight (a + b) ≤
      criticalHeight a + criticalHeight b + 1 := by
  by_cases hab0 : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simp
  have habPos : 0 < a + b := Nat.pos_of_ne_zero hab0
  have hA := threePow_le_twoPow_criticalHeight_succ a
  have hB := threePow_le_twoPow_criticalHeight_succ b
  have hUpper :
      3 ^ (a + b) ≤
        2 ^ (criticalHeight a + criticalHeight b + 2) := by
    have hExp :
        (criticalHeight a + 1) + (criticalHeight b + 1) =
          criticalHeight a + criticalHeight b + 2 := by omega
    calc
      3 ^ (a + b) = 3 ^ a * 3 ^ b := by rw [pow_add]
      _ ≤ 2 ^ (criticalHeight a + 1) * 2 ^ (criticalHeight b + 1) :=
        Nat.mul_le_mul hA hB
      _ = 2 ^ ((criticalHeight a + 1) + (criticalHeight b + 1)) := by
        rw [← pow_add]
      _ = 2 ^ (criticalHeight a + criticalHeight b + 2) := by rw [hExp]
  have hCrit := criticalHeight_pow_lt_threePow habPos
  by_contra hnot
  have hExp :
      criticalHeight a + criticalHeight b + 2 ≤ criticalHeight (a + b) := by
    omega
  have hPowLe :
      2 ^ (criticalHeight a + criticalHeight b + 2) ≤
        2 ^ criticalHeight (a + b) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExp
  have hContra :
      3 ^ (a + b) < 3 ^ (a + b) :=
    lt_of_le_of_lt hUpper (lt_of_le_of_lt hPowLe hCrit)
  exact (Nat.lt_irrefl _ hContra)

/-- additive critical carry。 -/
def criticalCarry (a b : ℕ) : ℕ :=
  criticalHeight (a + b) -
    (criticalHeight a + criticalHeight b)

/-- critical roof の exact addition formula。 -/
theorem criticalHeight_add_eq
    (a b : ℕ) :
    criticalHeight (a + b) =
      criticalHeight a + criticalHeight b + criticalCarry a b := by
  have hle := criticalHeight_add_lower a b
  unfold criticalCarry
  omega

/-- carry は高々1。 -/
theorem criticalCarry_le_one
    (a b : ℕ) :
    criticalCarry a b ≤ 1 := by
  have hUpper := criticalHeight_add_upper a b
  have hEq := criticalHeight_add_eq a b
  omega

/-- carry は 0 または 1。 -/
theorem criticalCarry_eq_zero_or_one
    (a b : ℕ) :
    criticalCarry a b = 0 ∨ criticalCarry a b = 1 := by
  have h := criticalCarry_le_one a b
  omega

/-- 三分割で carry の総量は括弧付けに依存しない。 -/
theorem criticalCarry_cocycle
    (a b c : ℕ) :
    criticalCarry a b + criticalCarry (a + b) c =
      criticalCarry b c + criticalCarry a (b + c) := by
  have hAB := criticalHeight_add_eq a b
  have hABC1 := criticalHeight_add_eq (a + b) c
  have hBC := criticalHeight_add_eq b c
  have hABC2 := criticalHeight_add_eq a (b + c)
  rw [Nat.add_assoc] at hABC1
  omega

end Word
end Collatz2
