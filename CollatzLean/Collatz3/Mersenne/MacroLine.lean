import CollatzLean.Collatz3.Mersenne.Basic
import Mathlib.Tactic.Ring


/-!
# Collatz3 Mersenne: fixed `(d,r)` macro affine line

一つの `BlockData d r u x y` から、同じ block depth `d` と exit depth `r` を保つ
無限 affine family を exact に生成する。

parameter `s` に対して

* `u` は `2^(r+1) * s` 増える、
* source `x` は `2^(d+r+1) * s` 増える、
* endpoint `y` は `2 * 3^d * s` 増える。

これを独立した大きな structure にせず、三つの薄い lift function と derived theorem で持つ。
-/

namespace Collatz3
namespace Mersenne

/-- fixed `(d,r)` family の `u` parameter lift。 -/
def blockParameterLift (r u s : ℕ) : ℕ :=
  u + 2 ^ (r + 1) * s

/-- fixed `(d,r)` family の source lift。 -/
def blockSourceLift (d r x s : ℕ) : ℕ :=
  x + 2 ^ (d + r + 1) * s

/-- fixed `d` family の endpoint lift。 -/
def blockEndpointLift (d y s : ℕ) : ℕ :=
  y + 2 * 3 ^ d * s

/--
一つの Mersenne block realization は、同じ `(d,r)` を持つ affine line 全体へ lift できる。
-/
theorem BlockData.lift
    {d r u x y : ℕ}
    (h : BlockData d r u x y)
    (s : ℕ) :
    BlockData d r
      (blockParameterLift r u s)
      (blockSourceLift d r x s)
      (blockEndpointLift d y s) := by
  refine ⟨h.depth_pos, h.exitDepth_pos, ?_, ?_, ?_⟩
  · rcases h.end_odd with ⟨q, hq⟩
    refine ⟨q + 3 ^ d * s, ?_⟩
    unfold blockEndpointLift
    rw [hq]
    ring
  · unfold blockSourceLift blockParameterLift
    have hEq := h.startEquation
    calc
      x + 2 ^ (d + r + 1) * s + 1
          = (x + 1) + 2 ^ (d + r + 1) * s := by ring
      _ = 2 ^ d * u + 2 ^ (d + r + 1) * s := by rw [hEq]
      _ = 2 ^ d * (u + 2 ^ (r + 1) * s) := by
        rw [show d + r + 1 = d + (r + 1) by omega, pow_add]
        ring
  · unfold blockEndpointLift blockParameterLift
    have hEq := h.endEquation
    calc
      2 ^ r * (y + 2 * 3 ^ d * s) + 1
          = (2 ^ r * y + 1) + (2 ^ r * 2) * 3 ^ d * s := by ring
      _ = 3 ^ d * u + (2 ^ r * 2) * 3 ^ d * s := by rw [hEq]
      _ = 3 ^ d * (u + 2 ^ (r + 1) * s) := by
        rw [pow_succ]
        ring

end Mersenne
end Collatz3
