import CollatzLean.Collatz3.Core.Word

/-!
# Collatz3: word prefix two-depth

有限 exponent word の先頭 `k` odd steps までに消費した 2-adic depth を、
actual orbit や critical geometry に依存しない純粋な word 関数として定義する。
-/

namespace Collatz3
namespace Word

/-- valid word では prefix two-depth は一 step ごとに strict に増える。 -/
theorem prefixTwoDepth_strict_succ_of_valid
    {w : Word}
    (hValid : Valid w)
    {k : ℕ}
    (hk : k < oddSteps w) :
    prefixTwoDepth w k < prefixTwoDepth w (k + 1) := by
  induction w generalizing k with
  | nil =>
      simp [oddSteps] at hk
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTail : Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      cases k with
      | zero =>
          simpa [prefixTwoDepth] using he
      | succ k =>
          have hkTail : k < oddSteps tail := by
            simpa [oddSteps] using hk
          have hIH := ih hTail hkTail
          simpa [prefixTwoDepth] using Nat.add_lt_add_left hIH e

end Word
end Collatz3
