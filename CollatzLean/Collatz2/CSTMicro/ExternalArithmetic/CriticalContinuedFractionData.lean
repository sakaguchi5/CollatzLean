import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.StrongBoundaryMatch

/-!
# Critical continued-fraction data

`α = log 2 / log 3` の regular continued fraction から使う
numerator / denominator 列を、Boundary A の strong route が必要とする
最小限の arithmetic data として切り出す。

このファイルでは実数 `log` や `Real.convergent` との同定自体は行わない。
後段の Christoffel packet / Sturmian overlap が参照するのは

* numerator `p_j`,
* denominator `q_j`,
* start index,
* denominator positivity / monotonicity / cofinality,
* start 以降の strict previous-denominator growth,

だけである。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- critical slope `log 2 / log 3` の convergent data 用 interface。 -/
structure CriticalContinuedFractionData where
  p : ℕ → ℕ
  q : ℕ → ℕ
  start : ℕ
  start_ge_three : 3 ≤ start

  /-- relevant indices では numerator は正。 -/
  p_pos :
    ∀ j : ℕ,
      start ≤ j →
      0 < p j

  /-- relevant indices では denominator は正。 -/
  q_pos :
    ∀ j : ℕ,
      start ≤ j →
      0 < q j

  /-- denominator sequence は globally nondecreasing。 -/
  q_mono :
    ∀ j : ℕ,
      q j ≤ q (j + 1)

  /-- start 以降では previous denominator から strict に増える。 -/
  q_strict_previous :
    ∀ j : ℕ,
      start ≤ j →
      q (j - 1) < q j

  /-- denominator sequence 自身が start 以降 cofinal。 -/
  q_cofinal :
    ∀ N : ℕ, ∃ j : ℕ,
      start ≤ j ∧ N ≤ q j

namespace CriticalContinuedFractionData

/-- strong certified precision endpoint `q_j + q_{j+1} - 1`。 -/
def strongPrecision
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℕ :=
  strongDenominatorWindowUpper D.q j

/-- strong window の lower endpoint `q_{j-1}+q_j-1`。 -/
def strongLower
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℕ :=
  strongDenominatorWindowLower D.q j

@[simp] theorem strongPrecision_eq
    (D : CriticalContinuedFractionData)
    (j : ℕ) :
    D.strongPrecision j = D.q j + D.q (j + 1) - 1 := by
  rfl

@[simp] theorem strongLower_eq
    (D : CriticalContinuedFractionData)
    (j : ℕ) :
    D.strongLower j = D.q (j - 1) + D.q j - 1 := by
  rfl

end CriticalContinuedFractionData

end ExternalArithmetic
end CSTMicro
end Collatz2
