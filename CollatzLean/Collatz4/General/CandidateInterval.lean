import CollatzLean.Collatz4.Core.Forward

/-!
# Collatz4.General.CandidateInterval

有限候補を等差列として保持するための一般層。

-/

namespace Collatz4.General

/-- `start + step*i` で有限候補を列挙するためのデータ。 -/
structure ArithmeticFamily where
  start : ℕ
  step : ℕ
  count : ℕ
  deriving Repr

namespace ArithmeticFamily

/-- `Fin count` の添字が表す候補値。 -/
def value (f : ArithmeticFamily) (i : Fin f.count) : ℕ :=
  f.start + f.step * i.1

/-- 候補値は必ず開始値以上。 -/
theorem start_le_value (f : ArithmeticFamily) (i : Fin f.count) :
    f.start ≤ f.value i := by
  simp [value]

/-- 等差列のある添字が値 n を表す、という一般的な membership。 -/
def Contains (f : ArithmeticFamily) (n : ℕ) : Prop :=
  ∃ i : Fin f.count, f.value i = n

/-- 列挙された値は当然その family に含まれる。 -/
theorem contains_value (f : ArithmeticFamily) (i : Fin f.count) :
    f.Contains (f.value i) := by
  exact ⟨i, rfl⟩

end ArithmeticFamily

end Collatz4.General
