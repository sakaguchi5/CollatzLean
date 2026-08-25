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

一般 power-form 増分下界を `8 < 9` に specialize したもの。
-/
theorem beattyIndex_add_two_ge_add_three
    (k : ℕ) :
    beattyIndex k + 3 ≤ beattyIndex (k + 2) := by
  simpa using
    (beattyIndex_add_lower_of_twoPow_lt_threePow
      (k := k) (r := 2) (s := 3)
      (by norm_num : 2 ^ 3 < 3 ^ 2))

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
