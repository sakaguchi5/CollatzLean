import CollatzLean.Collatz3.CSTCarry.OneModFour

/-!
# Collatz3 CSTCarry: `3 mod 4` は先頭二 step が odd

`4n+3` は二進数で必ず `...11` で終わる。
standard Terras step では最初の像 `6n+5` も奇数なので、
parity prefix は必ず `11` になる。

`4n-1` (`n>0`) は `4(n-1)+3` と同じ族である。
-/

namespace Collatz3
namespace CSTCarry

/-- `3 mod 4` の非負 parameterization。 -/
def threeModFourSeed (n : ℕ) : ℕ :=
  4 * n + 3

/-- `4n+3` は奇数。 -/
theorem threeModFourSeed_not_even (n : ℕ) :
    ¬ Even (threeModFourSeed n) := by
  intro h
  rcases h with ⟨k, hk⟩
  unfold threeModFourSeed at hk
  omega

/-- `4n+3` の最初の Terras step は `6n+5`。 -/
theorem terrasStep_threeModFourSeed (n : ℕ) :
    terrasStep (threeModFourSeed n) = 6 * n + 5 := by
  rw [terrasStep, ite_eq_right (threeModFourSeed_not_even n)]
  unfold threeModFourSeed
  omega

/-- 最初の像 `6n+5` も奇数。 -/
theorem firstImage_threeModFour_not_even (n : ℕ) :
    ¬ Even (6 * n + 5) := by
  intro h
  rcases h with ⟨k, hk⟩
  omega

/-- `3 mod 4` では最初の二つの standard steps がともに odd branch。 -/
def StartsWithTwoOddSteps (x : ℕ) : Prop :=
  ¬ Even x ∧ ¬ Even (terrasStep x)

/-- `4n+3` は必ず parity prefix `11` を持つ。 -/
theorem threeModFour_startsWithTwoOddSteps (n : ℕ) :
    StartsWithTwoOddSteps (threeModFourSeed n) := by
  constructor
  · exact threeModFourSeed_not_even n
  · rw [terrasStep_threeModFourSeed]
    exact firstImage_threeModFour_not_even n

/-- `4n+3` の二 step 後の exact value。 -/
theorem terrasStep_sq_threeModFourSeed (n : ℕ) :
    terrasStep (terrasStep (threeModFourSeed n)) = 9 * n + 8 := by
  rw [terrasStep_threeModFourSeed]
  rw [terrasStep, ite_eq_right (firstImage_threeModFour_not_even n)]
  omega

/-- 正の `n` では `4n-1 = 4(n-1)+3`。 -/
theorem four_mul_sub_one_eq_threeModFourSeed
    {n : ℕ}
    (hn : 0 < n) :
    4 * n - 1 = threeModFourSeed (n - 1) := by
  unfold threeModFourSeed
  omega

/-- したがって `4n-1` (`n>0`) の parity prefix も必ず `11`。 -/
theorem four_mul_sub_one_startsWithTwoOddSteps
    {n : ℕ}
    (hn : 0 < n) :
    StartsWithTwoOddSteps (4 * n - 1) := by
  rw [four_mul_sub_one_eq_threeModFourSeed hn]
  exact threeModFour_startsWithTwoOddSteps (n - 1)

end CSTCarry
end Collatz3
