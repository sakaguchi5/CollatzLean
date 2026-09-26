import CollatzLean.Collatz4.Finite.Forward

/-!
# Collatz4.Finite.CandidateInterval

有限候補を等差列として保持するための一般層。

`ArithmeticFamily` は既存 API を保ちつつ、
`intervalFamily` によって「下端・上端・刻み」から候補数を自動生成できるようにする。
これにより各特殊化で候補数を独立に手入力する必要をなくす。
-/

namespace Collatz4.Finite

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

/--
閉区間 `lo ≤ x ≤ hi` を刻み `step` で列挙するときの候補数。

`step = 0` は特殊化では使わない。一般定義としては自然数除算の規約に従う。
-/
def intervalCount (lo hi step : ℕ) : ℕ :=
  if lo ≤ hi then (hi - lo) / step + 1 else 0

/--
下端・上端・刻みから等差候補 family を作る。
候補数は `intervalCount` から自動的に決まる。
-/
def intervalFamily (lo hi step : ℕ) : ArithmeticFamily :=
  ⟨lo, step, intervalCount lo hi step⟩

@[simp] theorem intervalFamily_start (lo hi step : ℕ) :
    (intervalFamily lo hi step).start = lo := rfl

@[simp] theorem intervalFamily_step (lo hi step : ℕ) :
    (intervalFamily lo hi step).step = step := rfl

@[simp] theorem intervalFamily_count (lo hi step : ℕ) :
    (intervalFamily lo hi step).count = intervalCount lo hi step := rfl

end Collatz4.Finite
