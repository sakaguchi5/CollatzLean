import CollatzLean.Collatz3.Critical.Beatty

/-!
# Collatz3: Beatty roof の加法 carry

`beattyIndex` は critical roof の整数高さであり、加法に対するずれは高々 1 である。

このファイルでは旧 `criticalCarry` の本質だけを、現在の `beattyIndex` から導く。
Record/Ferrers や actual orbit は import しない。
-/

namespace Collatz3
namespace Critical

/-- `2^h < 3^k` なら `h` は Beatty roof 以下。 -/
theorem le_beattyIndex_of_twoPow_lt_threePow
    {k h : ℕ}
    (hlt : 2 ^ h < 3 ^ k) :
    h ≤ beattyIndex k := by
  by_contra hnot
  have hIdxLt : beattyIndex k < h := by omega
  have hExp : beattyIndex k + 1 ≤ h := by omega
  have hPow :
      2 ^ (beattyIndex k + 1) ≤ 2 ^ h :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExp
  have hUpper := beattyIndex_upper k
  have hContra : 3 ^ k < 3 ^ k :=
    lt_of_le_of_lt (le_trans hUpper hPow) hlt
  exact (Nat.lt_irrefl _ hContra)

/-- critical terminal depth は常に strict contracting 側にある。 -/
theorem threePow_lt_twoPow_criticalTwoDepth
    (m : ℕ) :
    3 ^ m < 2 ^ criticalTwoDepth m := by
  have hLe := threePow_le_twoPow_criticalTwoDepth m
  have hDepthPos : 0 < criticalTwoDepth m := by
    simp [criticalTwoDepth]
  have hOdd : Odd (3 ^ m) :=
    (show Odd (3 : ℕ) by decide).pow
  have hEven : Even (2 ^ criticalTwoDepth m) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hDepthPos)
  rcases hOdd with ⟨a, ha⟩
  rcases hEven with ⟨b, hb⟩
  omega

/-- Beatty roof は加法について下から超加法的。 -/
theorem beattyIndex_add_lower
    (a b : ℕ) :
    beattyIndex a + beattyIndex b ≤ beattyIndex (a + b) := by
  by_cases ha0 : a = 0
  · subst a
    simp
  by_cases hb0 : b = 0
  · subst b
    simp
  have haPos : 0 < a := Nat.pos_of_ne_zero ha0
  have hbPos : 0 < b := Nat.pos_of_ne_zero hb0
  have hA := beattyIndex_lower_strict haPos
  have hB := beattyIndex_lower_strict hbPos
  have hRightPos : 0 < 2 ^ beattyIndex b :=
    Nat.pow_pos (by decide)
  have h1 :
      2 ^ beattyIndex a * 2 ^ beattyIndex b <
        3 ^ a * 2 ^ beattyIndex b :=
    (Nat.mul_lt_mul_right hRightPos).2 hA
  have h2 :
      3 ^ a * 2 ^ beattyIndex b ≤ 3 ^ a * 3 ^ b :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hB)
  have hPow :
      2 ^ (beattyIndex a + beattyIndex b) < 3 ^ (a + b) := by
    calc
      2 ^ (beattyIndex a + beattyIndex b)
          = 2 ^ beattyIndex a * 2 ^ beattyIndex b := by rw [pow_add]
      _ < 3 ^ a * 2 ^ beattyIndex b := h1
      _ ≤ 3 ^ a * 3 ^ b := h2
      _ = 3 ^ (a + b) := by rw [pow_add]
  exact le_beattyIndex_of_twoPow_lt_threePow hPow

/-- Beatty roof の additive excess は高々 1。 -/
theorem beattyIndex_add_upper
    (a b : ℕ) :
    beattyIndex (a + b) ≤ beattyIndex a + beattyIndex b + 1 := by
  have hA := beattyIndex_upper a
  have hB := beattyIndex_upper b
  have hUpper :
      3 ^ (a + b) ≤
        2 ^ ((beattyIndex a + beattyIndex b + 1) + 1) := by
    calc
      3 ^ (a + b) = 3 ^ a * 3 ^ b := by rw [pow_add]
      _ ≤ 2 ^ (beattyIndex a + 1) * 2 ^ (beattyIndex b + 1) :=
        Nat.mul_le_mul hA hB
      _ = 2 ^ ((beattyIndex a + 1) + (beattyIndex b + 1)) := by
        rw [← pow_add]
      _ = 2 ^ ((beattyIndex a + beattyIndex b + 1) + 1) := by
        congr 1
        omega
  exact beattyIndex_le_of_upper hUpper

/-- Beatty roof の additive carry。 -/
def beattyCarry (a b : ℕ) : ℕ :=
  beattyIndex (a + b) - (beattyIndex a + beattyIndex b)

/-- Beatty roof の exact addition formula。 -/
theorem beattyIndex_add_eq
    (a b : ℕ) :
    beattyIndex (a + b) =
      beattyIndex a + beattyIndex b + beattyCarry a b := by
  have hLe := beattyIndex_add_lower a b
  unfold beattyCarry
  omega

/-- Beatty carry は高々 1。 -/
theorem beattyCarry_le_one
    (a b : ℕ) :
    beattyCarry a b ≤ 1 := by
  have hUpper := beattyIndex_add_upper a b
  have hEq := beattyIndex_add_eq a b
  omega

/-- Beatty carry は 0 または 1。 -/
theorem beattyCarry_eq_zero_or_one
    (a b : ℕ) :
    beattyCarry a b = 0 ∨ beattyCarry a b = 1 := by
  have h := beattyCarry_le_one a b
  omega

/--
幅 `m` の critical terminal chord は、任意の positive local denominator `r` で
Beatty lower roof より strict に上にある。

`m * beattyIndex r < criticalTwoDepth m * r`
-/
theorem beattyIndex_below_criticalChord
    {m r : ℕ}
    (hm : 0 < m)
    (hr : 0 < r) :
    m * beattyIndex r < criticalTwoDepth m * r := by
  have hLower := beattyIndex_lower_strict hr
  have hTerminal := threePow_lt_twoPow_criticalTwoDepth m
  have hLowerRaisedRaw :=
    Nat.pow_lt_pow_left hLower (Nat.ne_of_gt hm)
  have hLowerRaised :
      2 ^ (beattyIndex r * m) < 3 ^ (r * m) := by
    calc
      2 ^ (beattyIndex r * m)
          = (2 ^ beattyIndex r) ^ m := by rw [pow_mul]
      _ < (3 ^ r) ^ m := hLowerRaisedRaw
      _ = 3 ^ (r * m) := by rw [pow_mul]
  have hTerminalRaisedRaw :=
    Nat.pow_lt_pow_left hTerminal (Nat.ne_of_gt hr)
  have hTerminalRaised :
      3 ^ (m * r) < 2 ^ (criticalTwoDepth m * r) := by
    calc
      3 ^ (m * r)
          = (3 ^ m) ^ r := by rw [pow_mul]
      _ < (2 ^ criticalTwoDepth m) ^ r := hTerminalRaisedRaw
      _ = 2 ^ (criticalTwoDepth m * r) := by rw [pow_mul]
  have hPow :
      2 ^ (m * beattyIndex r) <
        2 ^ (criticalTwoDepth m * r) := by
    calc
      2 ^ (m * beattyIndex r)
          = 2 ^ (beattyIndex r * m) := by rw [Nat.mul_comm]
      _ < 3 ^ (r * m) := hLowerRaised
      _ = 3 ^ (m * r) := by rw [Nat.mul_comm]
      _ < 2 ^ (criticalTwoDepth m * r) := hTerminalRaised
  by_contra hnot
  have hExp : criticalTwoDepth m * r ≤ m * beattyIndex r := by omega
  have hPowLe :
      2 ^ (criticalTwoDepth m * r) ≤ 2 ^ (m * beattyIndex r) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExp
  exact (not_lt_of_ge hPowLe) hPow

end Critical
end Collatz3
