import CollatzLean.Collatz3.Critical.Beatty
import CollatzLean.Collatz3.Core.PrefixDepth

/-!
# Collatz3: critical first-passage word

odd-only exponent word に対する first-passage の純粋な係数幾何。
actual Collatz run はここに混ぜない。

`m = oddSteps w` とすると、

* terminal two-depth は最初の critical depth `beattyIndex m + 1`、
* 各 proper odd cut の prefix depth は Beatty roof 以下、

だけを保持する。
-/

namespace Collatz3
namespace Word

/-- critical coefficient boundary を初めて越える exponent word。 -/
def CriticalFirstPassage
    (w : Word) : Prop :=
  twoSteps w = Critical.criticalTwoDepth (oddSteps w) ∧
    ∀ k : ℕ,
      k < oddSteps w →
      prefixTwoDepth w k ≤ Critical.beattyIndex k

namespace CriticalFirstPassage

/-- terminal total two-depth は critical depth に exact に一致。 -/
theorem totalTwoDepth_eq
    {w : Word}
    (h : CriticalFirstPassage w) :
    twoSteps w = Critical.criticalTwoDepth (oddSteps w) :=
  h.1

/-- 各 relevant odd cut の prefix depth は Beatty roof 以下。 -/
theorem prefixDepth_le_beatty
    {w : Word}
    (h : CriticalFirstPassage w)
    {k : ℕ}
    (hk : k < oddSteps w) :
    prefixTwoDepth w k ≤ Critical.beattyIndex k :=
  h.2 k hk

/-- critical first-passage word は空でない。 -/
theorem nonempty
    {w : Word}
    (h : CriticalFirstPassage w) :
    w ≠ [] := by
  intro hw
  subst w
  have hDepth := h.totalTwoDepth_eq
  have hFalse : (0 : ℕ) = 1 := by
    simp [Critical.criticalTwoDepth] at hDepth
  omega

/-- critical first-passage word の odd-step 数は正。 -/
theorem oddSteps_pos
    {w : Word}
    (h : CriticalFirstPassage w) :
    0 < oddSteps w := by
  simpa [oddSteps] using List.length_pos_of_ne_nil h.nonempty

/-- proper positive odd cut は係数的に expanding 側にある。 -/
theorem properCut_twoPow_lt_threePow
    {w : Word}
    (h : CriticalFirstPassage w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hk : k < oddSteps w) :
    2 ^ prefixTwoDepth w k < 3 ^ k := by
  have hDepth := h.prefixDepth_le_beatty hk
  have hPowLe :
      2 ^ prefixTwoDepth w k ≤
        2 ^ Critical.beattyIndex k :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  exact lt_of_le_of_lt hPowLe
    (Critical.beattyIndex_lower_strict hkPos)

/-- terminal coefficient は critical two-depth で contracting 側へ到達する。 -/
theorem terminal_threePow_le_twoPow
    {w : Word}
    (h : CriticalFirstPassage w) :
    3 ^ oddSteps w ≤ 2 ^ twoSteps w := by
  rw [h.totalTwoDepth_eq]
  exact Critical.threePow_le_twoPow_criticalTwoDepth (oddSteps w)

/-- terminal coefficient は実際には strict に contracting 側。 -/
theorem terminal_threePow_lt_twoPow
    {w : Word}
    (h : CriticalFirstPassage w) :
    3 ^ oddSteps w < 2 ^ twoSteps w := by
  have hLe := h.terminal_threePow_le_twoPow
  have hTwoPos : 0 < twoSteps w := by
    rw [h.totalTwoDepth_eq]
    simp [Critical.criticalTwoDepth]
  have hOdd : Odd (3 ^ oddSteps w) :=
    (show Odd (3 : ℕ) by decide).pow
  have hEven : Even (2 ^ twoSteps w) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hTwoPos)
  rcases hOdd with ⟨a, ha⟩
  rcases hEven with ⟨b, hb⟩
  omega

end CriticalFirstPassage

end Word
end Collatz3
