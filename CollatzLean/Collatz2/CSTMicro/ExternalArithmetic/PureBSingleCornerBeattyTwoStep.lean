import CollatzLean.Collatz2.CSTMicro.BeattyPositions

/-!
# Pure B single-corner: Beatty two-step gap

single-corner の最上段を局所化するための純粋 Beatty 補題。

`beattyIndex n = floor(n log₂ 3)` を実数対数で展開せず、既存の power inequality だけで

  beattyIndex (k + 2) >= beattyIndex k + 3

を証明する。

これは `9 > 8`、すなわち二 odd-step の間に dyadic depth が少なくとも 3 増えることの
exact integer 版である。
-/

namespace Collatz2
namespace CSTMicro

/-- Beatty index は n step 進めば少なくとも n 増える。 -/
theorem beattyIndex_add_le
    (k n : ℕ) :
    beattyIndex k + n ≤ beattyIndex (k + n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hStep :
          beattyIndex (k + n) + 1 ≤
            beattyIndex (k + n + 1) := by
        have h := beattyIndex_lt_succ (k + n)
        omega
      have hAdd :
          beattyIndex k + n + 1 ≤
            beattyIndex (k + n) + 1 :=
        Nat.add_le_add_right ih 1
      have h := hAdd.trans hStep
      simpa [Nat.add_assoc] using h

/--
二 odd-step では Beatty depth は少なくとも 3 増える。

もし増分が 2 しかなければ

  3^(k+2) ≤ 2^(beattyIndex k + 3)

となる一方、`2^beattyIndex k ≤ 3^k` と `9 > 8` から逆向き strict inequality が出る。
-/
theorem beattyIndex_add_two_ge_add_three
    (k : ℕ) :
    beattyIndex k + 3 ≤ beattyIndex (k + 2) := by
  have hCoarse :
      beattyIndex k + 2 ≤ beattyIndex (k + 2) := by
    simpa using beattyIndex_add_le k 2
  by_contra hnot
  have hUpperIndex :
      beattyIndex (k + 2) ≤ beattyIndex k + 2 := by
    omega
  have hEq :
      beattyIndex (k + 2) = beattyIndex k + 2 := by
    omega
  have hUpper := beattyIndex_upper (k + 2)
  rw [hEq] at hUpper
  have hLower := beattyIndex_lower k
  have hThree :
      3 ^ (k + 2) = 3 ^ k * 9 := by
    rw [pow_add]
    norm_num
  have hTwo :
      2 ^ (beattyIndex k + 3) =
        2 ^ beattyIndex k * 8 := by
    rw [pow_add]
    norm_num
  rw [hThree, hTwo] at hUpper
  have hUpper' :
      3 ^ k * 9 ≤ 3 ^ k * 8 := by
    calc
      3 ^ k * 9
          ≤ 2 ^ beattyIndex k * 8 := hUpper
      _ ≤ 3 ^ k * 8 := by
          exact Nat.mul_le_mul_right 8 hLower
  have hStrict :
      3 ^ k * 8 < 3 ^ k * 9 := by
    exact Nat.mul_lt_mul_of_pos_left
      (by norm_num : 8 < 9)
      (pow_pos (by norm_num : 0 < (3 : ℕ)) k)
  exact (not_lt_of_ge hUpper') hStrict

/-- gap 1 が二回連続することはない。 -/
theorem not_two_consecutive_beatty_gap_one
    (k : ℕ)
    (h₁ : beattyIndex (k + 1) = beattyIndex k + 1)
    (h₂ : beattyIndex (k + 2) = beattyIndex (k + 1) + 1) :
    False := by
  have hTwo := beattyIndex_add_two_ge_add_three k
  rw [h₂, h₁] at hTwo
  omega

end CSTMicro
end Collatz2
