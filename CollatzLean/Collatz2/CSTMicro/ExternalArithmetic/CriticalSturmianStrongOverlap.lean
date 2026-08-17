import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacket

/-!
# Critical Sturmian strong overlap target

strong precision

  q_j + q_{j+1} - 1

を生む finite combinatorial statement を odd/even branch に分けて切り出す。

odd j:
  LCP(S^(q_j) v, v) >= q_{j+1}-1

even j:
  LCP(S^(q_j) v, 0 S v) >= q_{j+1}-1

ここでは無限 word / LCP object を導入せず、必要な有限 range 上で
`criticalSturmianBit` が pointwise に一致することとして表す。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `0 S v` の bit。0 番目だけ zero、その後は critical word の同じ index。 -/
def zeroShiftCriticalBit (r : ℕ) : Bool :=
  match r with
  | 0 => false
  | n + 1 => criticalSturmianBit (n + 1)

/-- strong overlap で要求する長さ `q_{j+1}-1`。 -/
def criticalStrongOverlapLength
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℕ :=
  D.q (j + 1) - 1

/--
critical Sturmian word の corrected odd/even strong overlap。

これは次段で standard-word / Christoffel recurrence から実証すべき
純 combinatorial theorem slot。
-/
structure CriticalSturmianStrongOverlap
    (D : CriticalContinuedFractionData) where
  odd_overlap :
    ∀ j r : ℕ,
      D.start ≤ j →
      j % 2 = 1 →
      r < criticalStrongOverlapLength D j →
      criticalSturmianBit (D.q j + r) =
        criticalSturmianBit r

  even_overlap :
    ∀ j r : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      r < criticalStrongOverlapLength D j →
      criticalSturmianBit (D.q j + r) =
        zeroShiftCriticalBit r

namespace CriticalSturmianStrongOverlap

/-- odd branch を prefix-length statement として読み直す。 -/
theorem odd_prefix_agrees
    {D : CriticalContinuedFractionData}
    (O : CriticalSturmianStrongOverlap D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjOdd : j % 2 = 1) :
    ∀ r : ℕ,
      r < D.q (j + 1) - 1 →
      criticalSturmianBit (D.q j + r) =
        criticalSturmianBit r := by
  intro r hr
  exact O.odd_overlap j r hjStart hjOdd hr

/-- even corrected branch を prefix-length statement として読み直す。 -/
theorem even_prefix_agrees
    {D : CriticalContinuedFractionData}
    (O : CriticalSturmianStrongOverlap D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjEven : j % 2 = 0) :
    ∀ r : ℕ,
      r < D.q (j + 1) - 1 →
      criticalSturmianBit (D.q j + r) =
        zeroShiftCriticalBit r := by
  intro r hr
  exact O.even_overlap j r hjStart hjEven hr

end CriticalSturmianStrongOverlap

end ExternalArithmetic
end CSTMicro
end Collatz2
