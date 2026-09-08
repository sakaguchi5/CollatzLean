import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Collatz3: power-form Beatty index and critical terminal depth

実数対数を primitive にせず、`3^m ≤ 2^(q+1)` を初めて満たす `q` を
`beattyIndex m` とする。first-passage の terminal two-depth は
`beattyIndex m + 1` として扱う。
-/

namespace Collatz3
namespace Critical

/-- `3^m` を上から挟む 2 冪は必ず存在する。 -/
theorem existsBeattyUpper (m : ℕ) :
    ∃ q : ℕ, 3 ^ m ≤ 2 ^ (q + 1) := by
  induction m with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ m ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨q + 2, ?_⟩
      rw [pow_succ]
      have hmul :
          3 ^ m * 3 ≤ 2 ^ (q + 1) * 4 :=
        Nat.mul_le_mul hq (by norm_num)
      calc
        3 ^ m * 3 ≤ 2 ^ (q + 1) * 4 := hmul
        _ = 2 ^ ((q + 2) + 1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]

/-- `floor(m log₂ 3)` の power-form version。 -/
def beattyIndex (m : ℕ) : ℕ :=
  Nat.find (existsBeattyUpper m)

/-- Beatty index 自身は upper inequality を満たす。 -/
theorem beattyIndex_upper (m : ℕ) :
    3 ^ m ≤ 2 ^ (beattyIndex m + 1) := by
  exact Nat.find_spec (existsBeattyUpper m)

/-- Beatty index の最小性。 -/
theorem beattyIndex_le_of_upper
    {m q : ℕ}
    (h : 3 ^ m ≤ 2 ^ (q + 1)) :
    beattyIndex m ≤ q := by
  exact Nat.find_min' (existsBeattyUpper m) h

/-- Beatty index より下では upper inequality はまだ成立しない。 -/
theorem not_beatty_upper_below
    {m q : ℕ}
    (hq : q < beattyIndex m) :
    ¬ (3 ^ m ≤ 2 ^ (q + 1)) := by
  intro h
  have hMin := beattyIndex_le_of_upper h
  omega

/-- `2^beattyIndex ≤ 3^m`。 -/
theorem beattyIndex_lower (m : ℕ) :
    2 ^ beattyIndex m ≤ 3 ^ m := by
  let q := beattyIndex m
  by_cases hq0 : q = 0
  · have hIdx : beattyIndex m = 0 := by
      simpa [q] using hq0
    rw [hIdx]
    have hPos : 0 < 3 ^ m := Nat.pow_pos (by decide)
    omega
  · have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
    let r := q - 1
    have hrLt : r < q := by
      dsimp [r]
      omega
    have hNot :
        ¬ (3 ^ m ≤ 2 ^ (r + 1)) := by
      apply not_beatty_upper_below (m := m) (q := r)
      simpa [q] using hrLt
    have hrSucc : r + 1 = q := by
      dsimp [r]
      omega
    have hNotQ :
        ¬ (3 ^ m ≤ 2 ^ q) := by
      simpa [hrSucc] using hNot
    have hLt : 2 ^ q < 3 ^ m := by
      exact Nat.lt_of_not_ge hNotQ
    simpa [q] using Nat.le_of_lt hLt

/-- `m>0` では lower inequality は strict。 -/
theorem beattyIndex_lower_strict
    {m : ℕ}
    (hm : 0 < m) :
    2 ^ beattyIndex m < 3 ^ m := by
  let q := beattyIndex m
  have hqPos : 0 < q := by
    by_contra hq0
    have hqEq : q = 0 := by omega
    have hUpper := beattyIndex_upper m
    rw [show beattyIndex m = 0 by simpa [q] using hqEq] at hUpper
    have hThree : 3 ≤ 3 ^ m := by
      cases m with
      | zero => omega
      | succ t =>
          rw [pow_succ]
          have hp : 0 < 3 ^ t := Nat.pow_pos (by decide)
          nlinarith
    norm_num at hUpper
    omega
  let r := q - 1
  have hrLt : r < q := by
    simp [r]
    omega
  have hNot := not_beatty_upper_below (m := m) (q := r) (by simpa [q] using hrLt)
  have hrSucc : r + 1 = q := by
    simp [r]
    omega
  have hNot' : ¬ (3 ^ m ≤ 2 ^ q) := by
    simpa [hrSucc, q] using hNot
  have hLt : 2 ^ q < 3 ^ m := by
    exact Nat.lt_of_not_ge hNot'
  simpa [q] using hLt

/-- `beattyIndex 0 = 0`。 -/
@[simp] theorem beattyIndex_zero : beattyIndex 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply beattyIndex_le_of_upper
  norm_num

/-- Beatty index は一 step で strict に増加する。 -/
theorem beattyIndex_lt_succ (m : ℕ) :
    beattyIndex m < beattyIndex (m + 1) := by
  let q := beattyIndex m
  have hLower := beattyIndex_lower m
  have hStrict : 2 ^ (q + 1) < 3 ^ (m + 1) := by
    rw [pow_succ, pow_succ]
    have hp : 0 < 2 ^ q := Nat.pow_pos (by decide)
    nlinarith
  by_contra hNot
  have hLe : beattyIndex (m + 1) ≤ q := by omega
  have hUpper := beattyIndex_upper (m + 1)
  have hPow :
      2 ^ (beattyIndex (m + 1) + 1) ≤ 2 ^ (q + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
  exact (not_lt_of_ge (le_trans hUpper hPow)) hStrict

/-- first-passage terminal に対応する total two-depth。 -/
def criticalTwoDepth (m : ℕ) : ℕ :=
  beattyIndex m + 1

@[simp] theorem criticalTwoDepth_eq (m : ℕ) :
    criticalTwoDepth m = beattyIndex m + 1 := rfl

/-- `3^m` は critical terminal two-depth 以下の 2 冪に収まる。 -/
theorem threePow_le_twoPow_criticalTwoDepth (m : ℕ) :
    3 ^ m ≤ 2 ^ criticalTwoDepth m := by
  simpa [criticalTwoDepth] using beattyIndex_upper m

end Critical
end Collatz3
