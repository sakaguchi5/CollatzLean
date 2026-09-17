import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Mersenne.Word
import CollatzLean.Collatz3.Semantics.Runs
import Mathlib.Tactic.Ring

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Collatz3 Bridge: Mersenne block arithmetic から actual Runs へ

低層 `Mersenne.BlockData` は整数等式だけを保持する。
このファイルで初めて actual `OddStep / Runs` に接続し、

`x + 1 = 2^d u`
`2^r y + 1 = 3^d u`

から exponent word

`[1,...,1,r+1]`

が actual に実行されることを導く。
-/

namespace Collatz3
namespace Bridge

/--
Mersenne `BlockData` は `blockWord d r` を exact に実行する actual finite run を与える。
-/
theorem mersenneBlockData_runs
    {d r u x y : ℕ}
    (h : Mersenne.BlockData d r u x y) :
    Runs (Mersenne.blockWord d r) x y := by
  induction d generalizing u x with
  | zero =>
      have := h.depth_pos
      omega
  | succ d ih =>
      cases d with
      | zero =>
          have hBalance :
              2 * (2 ^ r * y + 1) = 3 * (x + 1) := by
            rw [h.endEquation, h.startEquation]
            norm_num
            ring
          have hEq : 2 ^ (r + 1) * y = 3 * x + 1 := by
            have hExpanded :
                2 ^ (r + 1) * y + 2 = 3 * x + 3 := by
              calc
                2 ^ (r + 1) * y + 2
                    = 2 * (2 ^ r * y + 1) := by
                        rw [pow_succ]
                        ring
                _ = 3 * (x + 1) := hBalance
                _ = 3 * x + 3 := by ring
            omega
          have hStep : OddStep (r + 1) x y := by
            exact ⟨by omega, hEq, h.end_odd⟩
          simpa [Mersenne.blockWord] using
            (Runs.cons hStep (Runs.nil y))
      | succ d =>
          have huPos : 0 < u := by
            by_contra hu
            have huZero : u = 0 :=
              Nat.eq_zero_of_not_pos hu
            have hStart := h.startEquation
            rw [huZero] at hStart
            simp at hStart
          let x₁ : ℕ := 2 ^ (d + 1) * (3 * u) - 1
          have hProdPos : 0 < 2 ^ (d + 1) * (3 * u) := by
            exact Nat.mul_pos (Arithmetic.twoPow_pos (d + 1)) (by positivity)
          have hx₁ :
              x₁ + 1 = 2 ^ (d + 1) * (3 * u) := by
            dsimp [x₁]
            exact Nat.sub_add_cancel (by omega)
          have hTailEnd :
              2 ^ r * y + 1 = 3 ^ (d + 1) * (3 * u) := by
            calc
              2 ^ r * y + 1
                  = 3 ^ ((d + 1) + 1) * u := h.endEquation
              _ = 3 ^ (d + 1) * (3 * u) := by
                    rw [pow_succ]
                    ring
          have hTail :
              Mersenne.BlockData (d + 1) r (3 * u) x₁ y := by
            exact ⟨by omega, h.exitDepth_pos, h.end_odd, hx₁, hTailEnd⟩
          have hBalance :
              2 * (x₁ + 1) = 3 * (x + 1) := by
            rw [hx₁, h.startEquation]
            simp only [pow_succ]
            ring
          have hHeadEq : 2 * x₁ = 3 * x + 1 := by
            have hExpanded : 2 * x₁ + 2 = 3 * x + 3 := by
              calc
                2 * x₁ + 2 = 2 * (x₁ + 1) := by ring
                _ = 3 * (x + 1) := hBalance
                _ = 3 * x + 3 := by ring
            omega
          have hHead : OddStep 1 x x₁ := by
            exact ⟨by norm_num, by simpa using hHeadEq, hTail.start_odd⟩
          have hTailRuns :
              Runs (Mersenne.blockWord (d + 1) r) x₁ y :=
            ih hTail
          have hAll := Runs.cons hHead hTailRuns
          simpa [Mersenne.blockWord, List.replicate_succ] using hAll

/-- 27 の one-zero Mersenne block: `27 → 41 → 31`。 -/
example : Runs [1, 2] 27 31 := by
  have hData : Mersenne.BlockData 2 1 7 27 31 := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num, by norm_num⟩
    exact ⟨15, by norm_num⟩
  simpa [Mersenne.blockWord] using mersenneBlockData_runs hData

/-- 55 の one-zero Mersenne block: `55 → 83 → 125 → 47`。 -/
example : Runs [1, 1, 3] 55 47 := by
  have hData : Mersenne.BlockData 3 2 7 55 47 := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num, by norm_num⟩
    exact ⟨23, by norm_num⟩
  simpa [Mersenne.blockWord] using mersenneBlockData_runs hData

/-- 59 の one-zero Mersenne block: `59 → 89 → 67`。 -/
example : Runs [1, 2] 59 67 := by
  have hData : Mersenne.BlockData 2 1 15 59 67 := by
    refine ⟨by norm_num, by norm_num, ?_, by norm_num, by norm_num⟩
    exact ⟨33, by norm_num⟩
  simpa [Mersenne.blockWord] using mersenneBlockData_runs hData

end Bridge
end Collatz3
