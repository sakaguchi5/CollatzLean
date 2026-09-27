import Mathlib.Algebra.Group.Nat.Even

/-!
# Collatz3 CSTCarry: `1 mod 4` の即時下降

standard Terras step

* 偶数: `x / 2`
* 奇数: `(3x+1) / 2`

を直接定義し、`4n+1`（したがって正の範囲では `4n-3` と同じ合同類）が
2 standard steps で必ず初期値より下へ落ちることを証明する。

このファイルは first-passage / Ferrers / 2-adic residue に依存しない薄い算術層である。
-/

namespace Collatz3
namespace CSTCarry

/-- standard Terras step。 -/
def terrasStep (x : ℕ) : ℕ :=
  if Even x then x / 2 else (3 * x + 1) / 2

/-- `1 mod 4` の自然な非負 parameterization。 -/
def oneModFourSeed (n : ℕ) : ℕ :=
  4 * n + 1

/-- `4n+1` は奇数。 -/
theorem oneModFourSeed_not_even (n : ℕ) :
    ¬ Even (oneModFourSeed n) := by
  intro h
  rcases h with ⟨k, hk⟩
  unfold oneModFourSeed at hk
  omega

/-- `4n+1` の最初の Terras step は exact に `6n+2`。 -/
theorem terrasStep_oneModFourSeed (n : ℕ) :
    terrasStep (oneModFourSeed n) = 6 * n + 2 := by
  rw [terrasStep, ite_eq_right (oneModFourSeed_not_even n)]
  unfold oneModFourSeed
  omega

/-- 最初の像 `6n+2` は偶数。 -/
theorem firstImage_even (n : ℕ) :
    Even (6 * n + 2) := by
  refine ⟨3 * n + 1, ?_⟩
  omega

/-- `4n+1` は2 standard steps で exact に `3n+1` へ移る。 -/
theorem terrasStep_sq_oneModFourSeed (n : ℕ) :
    terrasStep (terrasStep (oneModFourSeed n)) = 3 * n + 1 := by
  rw [terrasStep_oneModFourSeed]
  rw [terrasStep, ite_eq_left (firstImage_even n)]
  omega

/-- `n>0` なら `4n+1` は2 standard steps で strict に初期値未満へ落ちる。 -/
theorem terrasStep_sq_oneModFourSeed_lt
    {n : ℕ}
    (hn : 0 < n) :
    terrasStep (terrasStep (oneModFourSeed n)) < oneModFourSeed n := by
  rw [terrasStep_sq_oneModFourSeed]
  unfold oneModFourSeed
  omega

/-- 正の `n` では `4n-3` を `4(n-1)+1` として読み直せる。 -/
theorem four_mul_sub_three_eq_oneModFourSeed
    {n : ℕ}
    (hn : 0 < n) :
    4 * n - 3 = oneModFourSeed (n - 1) := by
  unfold oneModFourSeed
  omega

/-- `n>1` の `4n-3` の最初の standard step は exact に `6n-4`。 -/
theorem terrasStep_four_mul_sub_three
    {n : ℕ}
    (hn : 1 < n) :
    terrasStep (4 * n - 3) = 6 * n - 4 := by
  have hn0 : 0 < n := by omega
  rw [four_mul_sub_three_eq_oneModFourSeed hn0]
  rw [terrasStep_oneModFourSeed]
  omega

/-- `n>1` では最初の step は初期値より大きい。 -/
theorem four_mul_sub_three_lt_firstStep
    {n : ℕ}
    (hn : 1 < n) :
    4 * n - 3 < terrasStep (4 * n - 3) := by
  rw [terrasStep_four_mul_sub_three hn]
  omega

/-- `n>1` の `4n-3` は2 standard steps で exact に `3n-2` へ移る。 -/
theorem terrasStep_sq_four_mul_sub_three
    {n : ℕ}
    (hn : 1 < n) :
    terrasStep (terrasStep (4 * n - 3)) = 3 * n - 2 := by
  have hn0 : 0 < n := by omega
  rw [four_mul_sub_three_eq_oneModFourSeed hn0]
  rw [terrasStep_sq_oneModFourSeed]
  omega

/-- `n>1` の `4n-3` は2 standard steps で必ず初期値未満へ落ちる。 -/
theorem terrasStep_sq_four_mul_sub_three_lt
    {n : ℕ}
    (hn : 1 < n) :
    terrasStep (terrasStep (4 * n - 3)) < 4 * n - 3 := by
  rw [terrasStep_sq_four_mul_sub_three hn]
  omega

/-- 「2 standard steps 以内で初期値より下」の局所 CST 条件。 -/
def TwoStepDescent (x : ℕ) : Prop :=
  terrasStep (terrasStep x) < x

/-- `4n-3`, `n>1` はすべて `TwoStepDescent` を満たす。 -/
theorem four_mul_sub_three_twoStepDescent
    {n : ℕ}
    (hn : 1 < n) :
    TwoStepDescent (4 * n - 3) := by
  exact terrasStep_sq_four_mul_sub_three_lt hn

/-- 2 step 後も自分以上である、という局所的な「最小候補」条件。 -/
def TwoStepMinimal (x : ℕ) : Prop :=
  x ≤ terrasStep (terrasStep x)

/-- `4n-3>1` は周期の最小点候補に必要な two-step minimality を満たせない。 -/
theorem four_mul_sub_three_not_twoStepMinimal
    {n : ℕ}
    (hn : 1 < n) :
    ¬ TwoStepMinimal (4 * n - 3) := by
  unfold TwoStepMinimal
  have h := terrasStep_sq_four_mul_sub_three_lt hn
  omega

end CSTCarry
end Collatz3
