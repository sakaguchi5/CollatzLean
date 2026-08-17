import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalContinuedFractionData

/-!
# Critical continued-fraction parity orientation

`alpha = log 2 / log 3` の regular convergent は parity ごとに target slope の
上下を交互に通る。corrected packet は全 index で total object なので、
actual convergent family について必要な global elementary facts をまとめる。

odd j:
  0 < p_j,
  2^q_j < 3^p_j

even j:
  3^p_j < 2^q_j

また regular continued-fraction denominator は全 index で positive とする。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure OrientedCriticalContinuedFractionData where
  base : CriticalContinuedFractionData

  q_pos_all :
    ∀ j : ℕ, 0 < base.q j

  odd_p_pos :
    ∀ j : ℕ,
      j % 2 = 1 →
      0 < base.p j

  odd_above :
    ∀ j : ℕ,
      j % 2 = 1 →
      2 ^ base.q j < 3 ^ base.p j

  even_below :
    ∀ j : ℕ,
      j % 2 = 0 →
      3 ^ base.p j < 2 ^ base.q j

namespace OrientedCriticalContinuedFractionData

/-- odd branch corrected denominator is positive. -/
theorem odd_gap_pos
    (D : OrientedCriticalContinuedFractionData)
    {j : ℕ}
    (hjOdd : j % 2 = 1) :
    0 < (3 : ℤ) ^ D.base.p j - (2 : ℤ) ^ D.base.q j := by
  apply sub_pos.mpr
  exact_mod_cast D.odd_above j hjOdd

/-- even branch corrected right gap is positive. -/
theorem even_gap_pos
    (D : OrientedCriticalContinuedFractionData)
    {j : ℕ}
    (hjEven : j % 2 = 0) :
    0 < (2 : ℤ) ^ D.base.q j - (3 : ℤ) ^ D.base.p j := by
  apply sub_pos.mpr
  exact_mod_cast D.even_below j hjEven

end OrientedCriticalContinuedFractionData

end ExternalArithmetic
end CSTMicro
end Collatz2
