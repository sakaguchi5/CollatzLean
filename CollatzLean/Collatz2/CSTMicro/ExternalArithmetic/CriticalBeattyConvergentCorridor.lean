import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalSturmianStrongOverlap

/-!
# Convergent height corridor -> strong Sturmian overlap

strong overlap を直接 black box にせず、continued-fraction approximation から
自然に得るべき critical-height shift law に一段下げる。

odd convergent では overlap range 全体で

  h(q_j+r) = p_j + h(r),

even convergent では first shifted bit だけ flat で、その後

  h(q_j+r) = p_j + h(r)  (r>0)

となる。ここから Bool-level strong overlap を純算術で導く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalBeattyConvergentCorridor
    (D : CriticalContinuedFractionData) where
  odd_height_shift :
    ∀ j r : ℕ,
      D.start ≤ j →
      j % 2 = 1 →
      r ≤ criticalStrongOverlapLength D j →
      criticalPrefixHeight (D.q j + r) =
        D.p j + criticalPrefixHeight r

  even_first_flat :
    ∀ j : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      criticalSturmianBit (D.q j) = false

  even_height_shift_pos :
    ∀ j r : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      0 < r →
      r ≤ criticalStrongOverlapLength D j →
      criticalPrefixHeight (D.q j + r) =
        D.p j + criticalPrefixHeight r

private theorem criticalBit_eq_of_height_shift
    {a b c : ℕ}
    (h0 : criticalPrefixHeight a = c + criticalPrefixHeight b)
    (h1 : criticalPrefixHeight (a + 1) =
      c + criticalPrefixHeight (b + 1)) :
    criticalSturmianBit a = criticalSturmianBit b := by
  have ha := criticalPrefixHeight_step a
  have hb := criticalPrefixHeight_step b
  rw [h0, h1] at ha
  have hbit :
      bitNat (criticalSturmianBit a) =
        bitNat (criticalSturmianBit b) := by
    omega
  cases hA : criticalSturmianBit a <;>
    cases hB : criticalSturmianBit b <;>
    simp [hA, hB, bitNat] at hbit ⊢

namespace CriticalBeattyConvergentCorridor

/-- height corridor formally implies the odd/even strong overlap object. -/
theorem toCriticalSturmianStrongOverlap
    {D : CriticalContinuedFractionData}
    (C : CriticalBeattyConvergentCorridor D) :
    CriticalSturmianStrongOverlap D := by
  refine {
    odd_overlap := ?_
    even_overlap := ?_
  }
  · intro j r hjStart hjOdd hr
    have hr0 := C.odd_height_shift j r hjStart hjOdd (by omega)
    have hr1 := C.odd_height_shift j (r + 1) hjStart hjOdd (by omega)
    have h :=
      criticalBit_eq_of_height_shift
        (a := D.q j + r)
        (b := r)
        (c := D.p j)
        hr0
        (by
          simpa [Nat.add_assoc] using hr1)
    exact h
  · intro j r hjStart hjEven hr
    cases r with
    | zero =>
        simpa [zeroShiftCriticalBit] using
          C.even_first_flat j hjStart hjEven
    | succ r =>
        have h0 :=
          C.even_height_shift_pos j (r + 1) hjStart hjEven
            (by omega) (by omega)
        have h1 :=
          C.even_height_shift_pos j (r + 2) hjStart hjEven
            (by omega) (by omega)
        have h :=
          criticalBit_eq_of_height_shift
            (a := D.q j + (r + 1))
            (b := r + 1)
            (c := D.p j)
            h0
            (by
              simpa [Nat.add_assoc] using h1)
        simpa [zeroShiftCriticalBit] using h

end CriticalBeattyConvergentCorridor

end ExternalArithmetic
end CSTMicro
end Collatz2
