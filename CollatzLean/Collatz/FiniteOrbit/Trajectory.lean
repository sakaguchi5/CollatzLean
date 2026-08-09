import CollatzLean.Collatz.Word.Basic

/-!
# 明示的有限trajectory

中間値をTypeデータとして保持する。`Runs : Prop`からデータを選択する設計を避け、
order reversalやsuffix解析で中間状態へ直接アクセスできるようにする。
-/

namespace Collatz
namespace FiniteOrbit

/-- 長さ`length`の明示的odd-only有限trajectory。 -/
structure Trajectory where
  length : ℕ
  value : ℕ → ℕ
  exponent : ℕ → ℕ
  exponent_pos : ∀ t, t < length → 0 < exponent t
  value_odd : ∀ t, t ≤ length → Odd (value t)
  step : ∀ t, t < length →
    2 ^ exponent t * value (t + 1) = 3 * value t + 1

namespace Trajectory

/-- 開始値。 -/
def start (T : Trajectory) : ℕ := T.value 0

/-- 終了値。 -/
def finish (T : Trajectory) : ℕ := T.value T.length

/-- trajectoryが使用する指数語。 -/
def word (T : Trajectory) : Collatz.Word :=
  List.ofFn (fun i : Fin T.length => T.exponent i.1)

@[simp] theorem word_length (T : Trajectory) : T.word.length = T.length := by
  simp [word]

end Trajectory
end FiniteOrbit
end Collatz
