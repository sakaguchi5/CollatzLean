import CollatzLean.Collatz3.CSTCarry.CarryBudgetBlock
import CollatzLean.Collatz3.Critical.RecordCarryBlockExact

/-!
# Collatz3 CSTCarry: record block の shifted Beatty roof

roof cut `a` から local index `j` だけ進んだ global Beatty height を
start roof から相対化する。

`shiftedBeattyIndex a j = beattyIndex (a+j) - beattyIndex a`

Beatty addition formula により exact に

`shiftedBeattyIndex a j = beattyIndex j + beattyCarry a j`

となる。

特に terminal block で `a+r=m` かつ terminal carry `0` なら

`criticalTwoDepth m = beattyIndex a + criticalTwoDepth r`

であり、whole binary modulus が local critical modulus と exact に factor する。
-/

namespace Collatz3
namespace Critical

/-- roof anchor `a` から見た相対 Beatty height。 -/
def shiftedBeattyIndex (a j : ℕ) : ℕ :=
  beattyIndex (a + j) - beattyIndex a

@[simp] theorem shiftedBeattyIndex_zero
    (a : ℕ) :
    shiftedBeattyIndex a 0 = 0 := by
  simp [shiftedBeattyIndex]

/-- shifted roof は local Beatty roof と additive carry の和。 -/
theorem shiftedBeattyIndex_eq
    (a j : ℕ) :
    shiftedBeattyIndex a j =
      beattyIndex j + beattyCarry a j := by
  have hAdd := beattyIndex_add_eq a j
  unfold shiftedBeattyIndex
  omega

/-- shifted roof は standard local Beatty roof 以上。 -/
theorem beattyIndex_le_shiftedBeattyIndex
    (a j : ℕ) :
    beattyIndex j ≤ shiftedBeattyIndex a j := by
  rw [shiftedBeattyIndex_eq]
  omega

/-- shifted roof は standard local roof より高々一段だけ上。 -/
theorem shiftedBeattyIndex_le_beattyIndex_add_one
    (a j : ℕ) :
    shiftedBeattyIndex a j ≤ beattyIndex j + 1 := by
  rw [shiftedBeattyIndex_eq]
  have hCarry := beattyCarry_le_one a j
  omega

/-- carry `0` なら shifted roof は standard local roof と一致。 -/
theorem shiftedBeattyIndex_eq_beatty_of_carry_zero
    {a j : ℕ}
    (hZero : beattyCarry a j = 0) :
    shiftedBeattyIndex a j = beattyIndex j := by
  rw [shiftedBeattyIndex_eq, hZero]
  omega

/-- carry `1` なら shifted roof は local critical depth に一致。 -/
theorem shiftedBeattyIndex_eq_criticalTwoDepth_of_carry_one
    {a j : ℕ}
    (hOne : beattyCarry a j = 1) :
    shiftedBeattyIndex a j = criticalTwoDepth j := by
  rw [shiftedBeattyIndex_eq, hOne]
  unfold criticalTwoDepth
  omega

/--
terminal carry `0` の exact depth factorization。

`a+r=m` かつ `beattyCarry a r=0` なら
`H_m = beattyIndex a + H_r`。
-/
theorem criticalTwoDepth_eq_beatty_add_of_terminal_carry_zero
    {m a r : ℕ}
    (hTerminal : a + r = m)
    (hZero : beattyCarry a r = 0) :
    criticalTwoDepth m =
      beattyIndex a + criticalTwoDepth r := by
  have hAdd := beattyIndex_add_eq a r
  rw [hZero, Nat.add_zero, hTerminal] at hAdd
  unfold criticalTwoDepth
  omega

/-- terminal carry `0` では binary modulus も exact に factor する。 -/
theorem twoPow_criticalTwoDepth_eq_mul_of_terminal_carry_zero
    {m a r : ℕ}
    (hTerminal : a + r = m)
    (hZero : beattyCarry a r = 0) :
    2 ^ criticalTwoDepth m =
      2 ^ beattyIndex a * 2 ^ criticalTwoDepth r := by
  rw [criticalTwoDepth_eq_beatty_add_of_terminal_carry_zero
        hTerminal hZero]
  exact pow_add 2 (beattyIndex a) (criticalTwoDepth r)

/-- interior carry `1` では block endpoint roof が `beattyIndex a + H_r`。 -/
theorem beattyIndex_add_eq_beatty_add_criticalTwoDepth_of_carry_one
    {a r : ℕ}
    (hOne : beattyCarry a r = 1) :
    beattyIndex (a + r) =
      beattyIndex a + criticalTwoDepth r := by
  have hAdd := beattyIndex_add_eq a r
  rw [hOne] at hAdd
  unfold criticalTwoDepth
  omega

end Critical
end Collatz3
