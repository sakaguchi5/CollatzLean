import CollatzLean.Collatz3.Mersenne.ExitDepth
import CollatzLean.Collatz3.Binary.BoundedDefect
import Mathlib.Tactic.NormNum


/-!
# Collatz3 Mersenne: one-zero exit と三つの算術領域

one-zero source の macro endpoint だけを薄い existential relation `OneZeroExit` として保存する。

`k,n` 平面は logarithm や bitLength を primitive にせず、2冪・3冪の比較だけで三領域へ分ける。

* stable: `3^k + 1 < 2^n`
* overlap: `2^n ≤ 3^k + 1` かつ `3^k < 2^(2n)`
* periodic: `2^(2n) ≤ 3^k`

この三分割は後段の conditional escape theorem の共通入口になる。
-/

namespace Collatz3
namespace Mersenne

/-- one-zero source からの exact Mersenne macro endpoint。 -/
def OneZeroExit (k n y : ℕ) : Prop :=
  ∃ x r : ℕ,
    IsOneZeroSource k n x ∧
      BlockData k r (2 ^ n - 1) x y

namespace OneZeroExit

/-- one-zero exit には source と exit depth が付随する。 -/
theorem exists_blockData
    {k n y : ℕ}
    (h : OneZeroExit k n y) :
    ∃ x r : ℕ,
      IsOneZeroSource k n x ∧
        BlockData k r (2 ^ n - 1) x y := h

/-- one-zero exit の width は少なくとも 2。 -/
theorem width_ge_two
    {k n y : ℕ}
    (h : OneZeroExit k n y) :
    2 ≤ n := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  exact hSource.width_ge_two

/-- one-zero exit は、ある正の exit depth で exact macro equation を満たす。 -/
theorem exists_exitDepth_equation
    {k n y : ℕ}
    (h : OneZeroExit k n y) :
    ∃ r : ℕ,
      0 < r ∧ Odd y ∧
        2 ^ r * y + 1 = 3 ^ k * (2 ^ n - 1) := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  exact ⟨r, hBlock.exitDepth_pos, hBlock.end_odd, hBlock.endEquation⟩

/-- `n≥3`、zero position が偶数なら exit equation は `2*y+1` 形。 -/
theorem evenPosition_equation
    {j n y : ℕ}
    (hn : 3 ≤ n)
    (h : OneZeroExit (2 * j) n y) :
    2 * y + 1 = 3 ^ (2 * j) * (2 ^ n - 1) := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  have hr := exitDepth_eq_one_of_evenPosition (j := j) hn hBlock
  subst r
  simpa using hBlock.endEquation

/-- `n≥3`、zero position が奇数なら exit equation は `4*y+1` 形。 -/
theorem oddPosition_equation
    {j n y : ℕ}
    (hn : 3 ≤ n)
    (h : OneZeroExit (2 * j + 1) n y) :
    4 * y + 1 = 3 ^ (2 * j + 1) * (2 ^ n - 1) := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  have hr := exitDepth_eq_two_of_oddPosition (j := j) hn hBlock
  subst r
  have hEq := hBlock.endEquation
  norm_num at hEq
  simpa using hEq

end OneZeroExit

/-- `2^n` が `3^k` を完全に越えた安定領域。 -/
def InStableRegion (k n : ℕ) : Prop :=
  3 ^ k + 1 < 2 ^ n

/-- `3^k` が高々二つの `n`-bit block に跨る overlap 領域。 -/
def InOverlapRegion (k n : ℕ) : Prop :=
  2 ^ n ≤ 3 ^ k + 1 ∧
    3 ^ k < 2 ^ (2 * n)

/-- 少なくとも二つの full `n`-bit periods を置ける periodic 領域。 -/
def InPeriodicRegion (k n : ℕ) : Prop :=
  2 ^ (2 * n) ≤ 3 ^ k

/-- 任意の `(k,n)` は stable / overlap / periodic の三領域のどれかに入る。 -/
theorem oneZeroRegion_trichotomy (k n : ℕ) :
    InStableRegion k n ∨
      InOverlapRegion k n ∨
        InPeriodicRegion k n := by
  by_cases hStable : 3 ^ k + 1 < 2 ^ n
  · exact Or.inl hStable
  · have hLow : 2 ^ n ≤ 3 ^ k + 1 := by omega
    by_cases hPeriodic : 2 ^ (2 * n) ≤ 3 ^ k
    · exact Or.inr (Or.inr hPeriodic)
    · have hHigh : 3 ^ k < 2 ^ (2 * n) := by omega
      exact Or.inr (Or.inl ⟨hLow, hHigh⟩)

end Mersenne
end Collatz3
