import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Collatz3 experimental: 0/1 carry を持つ整数値屋根

Collatz3 全面書き換え前の数学実験層。
現行の `Critical.Beatty` / `Critical.Profile` / `Ferrers` には依存しない。

ここでは整数値屋根 `β : ℕ → ℕ` について、加法誤差が高々 `1` であることだけを
原始条件として置く。

`β(a) + β(b) ≤ β(a+b) ≤ β(a) + β(b) + 1`

carry 自体や chord 不等式は field に保存せず、すべてこの条件から導く。
-/

namespace Collatz3
namespace Experimental

/--
整数値屋根 `β` の加法誤差が常に `0` または `1` に収まるための最小条件。

下側は超加法性、上側は「超過しても高々 1」を表す。
-/
def HasUnitCarry (β : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ,
    β a + β b ≤ β (a + b) ∧
      β (a + b) ≤ β a + β b + 1

/-- 屋根の加法 carry。`HasUnitCarry β` の下では theorem として `0` または `1` になる。 -/
def roofCarry (β : ℕ → ℕ) (a b : ℕ) : ℕ :=
  β (a + b) - (β a + β b)

/-- 幅 `m` に対する最小 terminal depth。 -/
def criticalDepth (β : ℕ → ℕ) (m : ℕ) : ℕ :=
  β m + 1

namespace HasUnitCarry

/-- 0/1-carry 屋根の exact addition formula。 -/
theorem add_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    β (a + b) = β a + β b + roofCarry β a b := by
  have hLower := (U a b).1
  unfold roofCarry
  omega

/-- carry は高々 `1`。 -/
theorem carry_le_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry β a b ≤ 1 := by
  have hLower := (U a b).1
  have hUpper := (U a b).2
  unfold roofCarry
  omega

/-- 最初の基本実験: carry は exact に `0` または `1`。 -/
theorem carry_eq_zero_or_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry β a b = 0 ∨ roofCarry β a b = 1 := by
  have h := carry_le_one U a b
  omega

/--
同じ幅 `r` を `n` 回足したときの下側評価。

`n * β(r) ≤ β(n*r)`。
-/
theorem mul_lower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ n r : ℕ,
      n * β r ≤ β (n * r)
  | 0, r => by
      simp
  | Nat.succ n, r => by
      have hPrev := mul_lower U n r
      have hAdd := (U (n * r) r).1
      calc
        (n + 1) * β r = n * β r + β r := by
          simp [Nat.add_mul]
        _ ≤ β (n * r) + β r := Nat.add_le_add_right hPrev (β r)
        _ ≤ β (n * r + r) := hAdd
        _ = β ((n + 1) * r) := by
          simp [Nat.add_mul]

/--
同じ幅 `r` を `n+1` 回足したときの sharp な上側評価。

carry が各接合で高々 `1` なので、接合回数 `n` だけを加えれば十分:
`β((n+1)r) ≤ (n+1)β(r) + n`。
-/
theorem mul_upper_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ n r : ℕ,
      β ((n + 1) * r) ≤ (n + 1) * β r + n
  | 0, r => by
      simp
  | Nat.succ n, r => by
      have hPrev := mul_upper_succ U n r
      have hAdd := (U ((n + 1) * r) r).2
      calc
        β (((n + 1) + 1) * r) = β ((n + 1) * r + r) := by
          congr 1
          simp [Nat.add_mul]
        _ ≤ β ((n + 1) * r) + β r + 1 := hAdd
        _ ≤ ((n + 1) * β r + n) + β r + 1 := by
          have h := Nat.add_le_add_right hPrev (β r + 1)
          simpa [Nat.add_assoc] using h
        _ = ((n + 1) + 1) * β r + (n + 1) := by
          simp only [Nat.add_mul]
          omega

/--
第二の基本実験: 0/1-carry だけから critical chord の strict 不等式が出る。

`m * β(r) < (β(m)+1) * r`。

現行 Collatz3 の `beattyIndex_below_criticalChord` に対応するが、
ここでは `2^H` と `3^m` を一切使わない。
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
      have hLower := mul_lower U m (n + 1)
      have hUpper := mul_upper_succ U n m
      calc
        m * β (n + 1) ≤ β (m * (n + 1)) := hLower
        _ = β ((n + 1) * m) := by
          rw [Nat.mul_comm]
        _ ≤ (n + 1) * β m + n := hUpper
        _ < (n + 1) * β m + (n + 1) := by
          omega
        _ = criticalDepth β m * (n + 1) := by
          unfold criticalDepth
          ring

end HasUnitCarry
end Experimental
end Collatz3
