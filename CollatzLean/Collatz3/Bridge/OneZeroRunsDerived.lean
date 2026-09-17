import CollatzLean.Collatz3.Mersenne.OneZeroRegions
import CollatzLean.Collatz3.Bridge.MersenneRuns

/-!
# Collatz3 Bridge: one-zero exit の actual exponent word

`OneZeroExit` は arithmetic relation として source / exit depth を隠している。
ここではその witness を actual `Runs` へ戻し、`n≥3` では zero position の偶奇から
末尾 exponent `2` / `3` が確定することを derived theorem として保存する。
-/

namespace Collatz3
namespace Bridge

/-- 任意の one-zero exit は対応する Mersenne block word を actual に実行する。 -/
theorem oneZeroExit_exists_runs
    {k n y : ℕ}
    (h : Mersenne.OneZeroExit k n y) :
    ∃ x r : ℕ,
      Mersenne.IsOneZeroSource k n x ∧
        Runs (Mersenne.blockWord k r) x y := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  exact ⟨x, r, hSource, mersenneBlockData_runs hBlock⟩

/-- `n≥3` で zero position が偶数なら actual block word の末尾 exponent は `2`。 -/
theorem oneZeroExit_exists_runs_of_evenPosition
    {j n y : ℕ}
    (hn : 3 ≤ n)
    (h : Mersenne.OneZeroExit (2 * j) n y) :
    ∃ x : ℕ,
      Mersenne.IsOneZeroSource (2 * j) n x ∧
        Runs (Mersenne.blockWord (2 * j) 1) x y := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  have hr := Mersenne.exitDepth_eq_one_of_evenPosition (j := j) hn hBlock
  subst r
  exact ⟨x, hSource, mersenneBlockData_runs hBlock⟩

/-- `n≥3` で zero position が奇数なら actual block word の末尾 exponent は `3`。 -/
theorem oneZeroExit_exists_runs_of_oddPosition
    {j n y : ℕ}
    (hn : 3 ≤ n)
    (h : Mersenne.OneZeroExit (2 * j + 1) n y) :
    ∃ x : ℕ,
      Mersenne.IsOneZeroSource (2 * j + 1) n x ∧
        Runs (Mersenne.blockWord (2 * j + 1) 2) x y := by
  rcases h with ⟨x, r, hSource, hBlock⟩
  have hr := Mersenne.exitDepth_eq_two_of_oddPosition (j := j) hn hBlock
  subst r
  exact ⟨x, hSource, mersenneBlockData_runs hBlock⟩

end Bridge
end Collatz3
