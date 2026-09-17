import CollatzLean.Collatz3.Binary.Runs
import CollatzLean.Collatz3.Binary.Basic

/-!
# Collatz3 Binary: run / periodic-break complexity

外部の digit-complexity theorem と接続するための最小語彙。

binary word 自体を正本とし、

* maximal run の個数
* period `p` だけずらした bit との不一致個数

だけを自然数として読む。
自然数 `x` に対する complexity predicate では `HasBitLength` を同時に要求し、
leading zero を自由に付加した非 canonical representation を除く。
-/

namespace Collatz3
namespace Binary

/-- binary word の maximal run 数。 -/
def runCount (bits : List Bool) : ℕ :=
  (binaryRuns bits).length

/-- 二つの Bool 列を先頭から比較した不一致個数。短い側が尽きたら比較を終える。 -/
def mismatchCount : List Bool → List Bool → ℕ
  | b :: bs, c :: cs =>
      (if b = c then 0 else 1) + mismatchCount bs cs
  | _, _ => 0

/-- period `p` だけ先の bit と異なる位置の個数。 -/
def periodBreakCount (p : ℕ) (bits : List Bool) : ℕ :=
  mismatchCount bits (bits.drop p)

@[simp] theorem mismatchCount_nil_left (bits : List Bool) :
    mismatchCount [] bits = 0 := rfl

@[simp] theorem mismatchCount_nil_right (bits : List Bool) :
    mismatchCount bits [] = 0 := by
  cases bits <;> rfl

@[simp] theorem mismatchCount_self (bits : List Bool) :
    mismatchCount bits bits = 0 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [mismatchCount, ih]

@[simp] theorem periodBreakCount_zero (bits : List Bool) :
    periodBreakCount 0 bits = 0 := by
  simp [periodBreakCount]

/-- `x` の canonical-length binary representation の run 数が `bound` 以下。 -/
def HasRunComplexityAtMost (x bound : ℕ) : Prop :=
  ∃ bits : List Bool,
    ∃ length : ℕ,
      RepresentsAtLength bits x length ∧
        HasBitLength x length ∧
        runCount bits ≤ bound

/-- `x` の canonical-length binary representation の period-break 数が `bound` 以下。 -/
def HasPeriodBreakAtMost (x period bound : ℕ) : Prop :=
  ∃ bits : List Bool,
    ∃ length : ℕ,
      RepresentsAtLength bits x length ∧
      HasBitLength x length ∧
      periodBreakCount period bits ≤ bound

namespace HasRunComplexityAtMost

/-- complexity 上限を緩めても性質は保存される。 -/
theorem mono
    {x a b : ℕ}
    (h : HasRunComplexityAtMost x a)
    (hab : a ≤ b) :
    HasRunComplexityAtMost x b := by
  rcases h with ⟨bits, length, hRep, hLen, hRun⟩
  exact ⟨bits, length, hRep, hLen, le_trans hRun hab⟩

end HasRunComplexityAtMost

namespace HasPeriodBreakAtMost

/-- period-break 上限を緩めても性質は保存される。 -/
theorem mono
    {x period a b : ℕ}
    (h : HasPeriodBreakAtMost x period a)
    (hab : a ≤ b) :
    HasPeriodBreakAtMost x period b := by
  rcases h with ⟨bits, length, hRep, hLen, hBreak⟩
  exact ⟨bits, length, hRep, hLen, le_trans hBreak hab⟩

end HasPeriodBreakAtMost

end Binary
end Collatz3
