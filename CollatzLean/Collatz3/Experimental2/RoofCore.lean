import Mathlib.Data.Nat.Basic

import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: 屋根の最小公理

`Experimental2` では、旧 `Experimental` の発見順ではなく数学的依存順に再構成する。

整数値屋根 `β : ℕ → ℕ` に対して、

* 下側の超加法性
* 上側の一単位誤差

を別々の薄い predicate として置く。

両方を合わせた `HasUnitCarry` から、反復評価や critical chord 不等式を theorem として導く。
-/

namespace Collatz3
namespace Experimental2

/-- 屋根の下側公理: 超加法性。 -/
def IsSuperadditiveRoof (β : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, β a + β b ≤ β (a + b)

/-- 屋根の上側公理: 加法誤差は高々 `1`。 -/
def HasUnitUpperDefect (β : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, β (a + b) ≤ β a + β b + 1

/-- 0/1-carry 屋根。二つの薄い公理を束ねるだけの定義。 -/
def HasUnitCarry (β : ℕ → ℕ) : Prop :=
  IsSuperadditiveRoof β ∧ HasUnitUpperDefect β

/-- 幅 `m` の critical depth。 -/
def criticalDepth (β : ℕ → ℕ) (m : ℕ) : ℕ :=
  β m + 1

namespace IsSuperadditiveRoof

/-- 超加法的な自然数値屋根は原点で必ず `0`。 -/
theorem zero_eq
    {β : ℕ → ℕ}
    (L : IsSuperadditiveRoof β) :
    β 0 = 0 := by
  have h : β 0 + β 0 ≤ β 0 := by
    simpa using L 0 0
  omega

/-- 同じ幅 `r` を `n` 回足した下側反復評価。 -/
theorem mul_lower
    {β : ℕ → ℕ}
    (L : IsSuperadditiveRoof β) :
    ∀ n r : ℕ, n * β r ≤ β (n * r)
  | 0, r => by simp
  | Nat.succ n, r => by
      have hPrev := L.mul_lower n r
      have hAdd := L (n * r) r
      calc
        (n + 1) * β r = n * β r + β r := by simp [Nat.add_mul]
        _ ≤ β (n * r) + β r := Nat.add_le_add_right hPrev (β r)
        _ ≤ β (n * r + r) := hAdd
        _ = β ((n + 1) * r) := by simp [Nat.add_mul]

end IsSuperadditiveRoof

namespace HasUnitUpperDefect

/-- 同じ幅 `r` を `n+1` 回足した sharp 上側反復評価。 -/
theorem mul_upper_succ
    {β : ℕ → ℕ}
    (H : HasUnitUpperDefect β) :
    ∀ n r : ℕ,
      β ((n + 1) * r) ≤ (n + 1) * β r + n
  | 0, r => by simp
  | Nat.succ n, r => by
      have hPrev := H.mul_upper_succ n r
      have hAdd := H ((n + 1) * r) r
      calc
        β (((n + 1) + 1) * r) = β ((n + 1) * r + r) := by
          congr 1
          simp [Nat.add_mul]
        _ ≤ β ((n + 1) * r) + β r + 1 := hAdd
        _ ≤ ((n + 1) * β r + n) + β r + 1 := by
          omega
        _ = ((n + 1) + 1) * β r + (n + 1) := by
          simp only [Nat.add_mul]
          omega

end HasUnitUpperDefect

namespace HasUnitCarry

/-- `HasUnitCarry` から下側公理を取り出す。 -/
theorem lower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    IsSuperadditiveRoof β :=
  U.1

/-- `HasUnitCarry` から上側公理を取り出す。 -/
theorem upper
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    HasUnitUpperDefect β :=
  U.2

/-- unit-carry 屋根の原点は `0`。 -/
theorem zero_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    β 0 = 0 :=
  U.lower.zero_eq

/-- 下側反復評価の wrapper。 -/
theorem mul_lower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n r : ℕ) :
    n * β r ≤ β (n * r) :=
  U.lower.mul_lower n r

/-- 上側反復評価の wrapper。 -/
theorem mul_upper_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n r : ℕ) :
    β ((n + 1) * r) ≤ (n + 1) * β r + n :=
  U.upper.mul_upper_succ n r

/--
unit-carry だけから出る strict critical chord。

`m * β(r) < (β(m)+1) * r`。
-/
theorem below_criticalChord
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m r : ℕ}
    (hr : 0 < r) :
    m * β r < criticalDepth β m * r := by
  cases r with
  | zero => omega
  | succ n =>
      have hLower := U.mul_lower m (n + 1)
      have hUpper := U.mul_upper_succ n m
      calc
        m * β (n + 1) ≤ β (m * (n + 1)) := hLower
        _ = β ((n + 1) * m) := by rw [Nat.mul_comm]
        _ ≤ (n + 1) * β m + n := hUpper
        _ < (n + 1) * β m + (n + 1) := by omega
        _ = criticalDepth β m * (n + 1) := by
          unfold criticalDepth
          ring

end HasUnitCarry
end Experimental2
end Collatz3
