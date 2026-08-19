import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelWronskian

/-!
# Corrected Christoffel Wronskian

raw Wronskian law を existing corrected Christoffel packet

odd j:
  P_j = φ_j
  Q_j = 3^p_j - 2^q_j

even j:
  P_j = 2^(q_j-1) - 3φ_j
  Q_j = 3(2^q_j - 3^p_j)

へ代入する。

raw determinant に含まれていた 3-power は correction と exact に相殺し、
consecutive corrected determinant は

  even j : -2^(q_j + q_(j+1) - 1)
  odd  j : +2^(q_j + q_(j+1) - 1)

になる。

したがって exponent は existing `strongPrecision j` と exact に一致する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- corrected consecutive determinant。 -/
def correctedChristoffelWronskianNext
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  correctedChristoffelP D j * correctedChristoffelQ D (j + 1) -
    correctedChristoffelP D (j + 1) * correctedChristoffelQ D j

/-- even `j` では corrected determinant は exact に `-2^strongPrecision`。 -/
theorem correctedChristoffelWronskianNext_eq_neg_twoPow_strongPrecision_of_even
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjEven : j % 2 = 0) :
    correctedChristoffelWronskianNext D j =
      -((2 : ℤ) ^ D.strongPrecision j) := by
  have hjNextOdd : (j + 1) % 2 = 1 := by
    omega
  have hqj : 0 < D.q j := D.q_pos j hjStart
  have hpNext : 0 < D.p (j + 1) :=
    D.p_pos (j + 1) (by omega)
  have hRaw := W.even_next j hjStart hjEven
  unfold criticalRawChristoffelWronskianNext
    criticalRawPowerGap at hRaw
  have hThree :
      3 * (3 : ℤ) ^ (D.p (j + 1) - 1) =
        (3 : ℤ) ^ D.p (j + 1) := by
    calc
      3 * (3 : ℤ) ^ (D.p (j + 1) - 1)
          = (3 : ℤ) ^ (D.p (j + 1) - 1) * 3 := by ring
      _ = (3 : ℤ) ^ ((D.p (j + 1) - 1) + 1) := by
            rw [pow_succ]
      _ = (3 : ℤ) ^ D.p (j + 1) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ D.p (j + 1))]
  unfold correctedChristoffelWronskianNext
  rw [correctedChristoffelP_even D hjEven]
  rw [correctedChristoffelQ_even D hjEven]
  rw [correctedChristoffelP_odd D hjNextOdd]
  rw [correctedChristoffelQ_odd D hjNextOdd]
  have hCollapsed :
      ((2 : ℤ) ^ (D.q j - 1) -
            3 * criticalChristoffelPhiAt D j) *
          ((3 : ℤ) ^ D.p (j + 1) - (2 : ℤ) ^ D.q (j + 1)) -
        criticalChristoffelPhiAt D (j + 1) *
          (3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j)) =
      -((2 : ℤ) ^ (D.q j - 1) *
        (2 : ℤ) ^ D.q (j + 1)) := by
    calc
      ((2 : ℤ) ^ (D.q j - 1) -
            3 * criticalChristoffelPhiAt D j) *
          ((3 : ℤ) ^ D.p (j + 1) - (2 : ℤ) ^ D.q (j + 1)) -
        criticalChristoffelPhiAt D (j + 1) *
          (3 * ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j))
          =
        -((2 : ℤ) ^ (D.q j - 1)) *
            ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1)) +
          3 *
            (criticalChristoffelPhiAt D j *
                ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1)) -
              criticalChristoffelPhiAt D (j + 1) *
                ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j)) := by ring
      _ =
        -((2 : ℤ) ^ (D.q j - 1)) *
            ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1)) -
          3 *
            ((2 : ℤ) ^ (D.q j - 1) *
              (3 : ℤ) ^ (D.p (j + 1) - 1)) := by
            rw [hRaw]
            ring
      _ =
        -((2 : ℤ) ^ (D.q j - 1) *
          (2 : ℤ) ^ D.q (j + 1)) := by
            have hAbsorb :
                3 *
                    ((2 : ℤ) ^ (D.q j - 1) *
                      (3 : ℤ) ^ (D.p (j + 1) - 1)) =
                  (2 : ℤ) ^ (D.q j - 1) *
                    (3 : ℤ) ^ D.p (j + 1) := by
              calc
                3 *
                    ((2 : ℤ) ^ (D.q j - 1) *
                      (3 : ℤ) ^ (D.p (j + 1) - 1))
                    =
                  (2 : ℤ) ^ (D.q j - 1) *
                    (3 * (3 : ℤ) ^ (D.p (j + 1) - 1)) := by
                      ring
                _ =
                  (2 : ℤ) ^ (D.q j - 1) *
                    (3 : ℤ) ^ D.p (j + 1) := by
                      rw [hThree]
            rw [hAbsorb]
            ring
  rw [hCollapsed]
  have hExp :
      (D.q j - 1) + D.q (j + 1) =
        D.q j + D.q (j + 1) - 1 := by
    omega
  rw [← pow_add]
  rw [hExp]
  rw [D.strongPrecision_eq]

/-- odd `j` では corrected determinant は exact に `+2^strongPrecision`。 -/
theorem correctedChristoffelWronskianNext_eq_twoPow_strongPrecision_of_odd
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjOdd : j % 2 = 1) :
    correctedChristoffelWronskianNext D j =
      (2 : ℤ) ^ D.strongPrecision j := by
  have hjNextEven : (j + 1) % 2 = 0 := by
    omega
  have hqNext : 0 < D.q (j + 1) :=
    D.q_pos (j + 1) (by omega)
  have hpj : 0 < D.p j := D.p_pos j hjStart
  have hRaw := W.odd_next j hjStart hjOdd
  unfold criticalRawChristoffelWronskianNext
    criticalRawPowerGap at hRaw
  have hThree :
      3 * (3 : ℤ) ^ (D.p j - 1) =
        (3 : ℤ) ^ D.p j := by
    calc
      3 * (3 : ℤ) ^ (D.p j - 1)
          = (3 : ℤ) ^ (D.p j - 1) * 3 := by ring
      _ = (3 : ℤ) ^ ((D.p j - 1) + 1) := by
            rw [pow_succ]
      _ = (3 : ℤ) ^ D.p j := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ D.p j)]
  unfold correctedChristoffelWronskianNext
  rw [correctedChristoffelP_odd D hjOdd]
  rw [correctedChristoffelQ_odd D hjOdd]
  rw [correctedChristoffelP_even D hjNextEven]
  rw [correctedChristoffelQ_even D hjNextEven]
  have hCollapsed :
      criticalChristoffelPhiAt D j *
          (3 * ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1))) -
        ((2 : ℤ) ^ (D.q (j + 1) - 1) -
            3 * criticalChristoffelPhiAt D (j + 1)) *
          ((3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j) =
      (2 : ℤ) ^ (D.q (j + 1) - 1) *
        (2 : ℤ) ^ D.q j := by
    calc
      criticalChristoffelPhiAt D j *
          (3 * ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1))) -
        ((2 : ℤ) ^ (D.q (j + 1) - 1) -
            3 * criticalChristoffelPhiAt D (j + 1)) *
          ((3 : ℤ) ^ D.p j - (2 : ℤ) ^ D.q j)
          =
        (2 : ℤ) ^ (D.q (j + 1) - 1) *
            ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) +
          3 *
            (criticalChristoffelPhiAt D j *
                ((2 : ℤ) ^ D.q (j + 1) - (3 : ℤ) ^ D.p (j + 1)) -
              criticalChristoffelPhiAt D (j + 1) *
                ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j)) := by ring
      _ =
        (2 : ℤ) ^ (D.q (j + 1) - 1) *
            ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) +
          3 *
            ((2 : ℤ) ^ (D.q (j + 1) - 1) *
              (3 : ℤ) ^ (D.p j - 1)) := by
            rw [hRaw]
      _ =
        (2 : ℤ) ^ (D.q (j + 1) - 1) *
          (2 : ℤ) ^ D.q j := by
            calc
              (2 : ℤ) ^ (D.q (j + 1) - 1) *
                    ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) +
                  3 *
                    ((2 : ℤ) ^ (D.q (j + 1) - 1) *
                      (3 : ℤ) ^ (D.p j - 1))
                  =
                (2 : ℤ) ^ (D.q (j + 1) - 1) *
                    ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) +
                  (2 : ℤ) ^ (D.q (j + 1) - 1) *
                    (3 * (3 : ℤ) ^ (D.p j - 1)) := by
                      ring
              _ =
                (2 : ℤ) ^ (D.q (j + 1) - 1) *
                    ((2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j) +
                  (2 : ℤ) ^ (D.q (j + 1) - 1) *
                    (3 : ℤ) ^ D.p j := by
                      rw [hThree]
              _ =
                (2 : ℤ) ^ (D.q (j + 1) - 1) *
                  (2 : ℤ) ^ D.q j := by
                      ring
  rw [hCollapsed]
  have hExp :
      (D.q (j + 1) - 1) + D.q j =
        D.q j + D.q (j + 1) - 1 := by
    omega
  rw [← pow_add]
  rw [hExp]
  rw [D.strongPrecision_eq]

/--
全 relevant index で corrected determinant は strong precision の exact signed power。
-/
theorem correctedChristoffelWronskianNext_signed_strongPrecision
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j) :
    (j % 2 = 0 ∧
        correctedChristoffelWronskianNext D j =
          -((2 : ℤ) ^ D.strongPrecision j)) ∨
      (j % 2 = 1 ∧
        correctedChristoffelWronskianNext D j =
          (2 : ℤ) ^ D.strongPrecision j) := by
  have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · right
    exact ⟨hjOdd,
      correctedChristoffelWronskianNext_eq_twoPow_strongPrecision_of_odd
        W hjStart hjOdd⟩
  · have hjEven : j % 2 = 0 := by omega
    left
    exact ⟨hjEven,
      correctedChristoffelWronskianNext_eq_neg_twoPow_strongPrecision_of_even
        W hjStart hjEven⟩

/-- corrected determinant は relevant index で nonzero。 -/
theorem correctedChristoffelWronskianNext_ne_zero
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j) :
    correctedChristoffelWronskianNext D j ≠ 0 := by
  rcases
      correctedChristoffelWronskianNext_signed_strongPrecision W hjStart with
    hEven | hOdd
  · rw [hEven.2]
    exact neg_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0))
  · rw [hOdd.2]
    exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)

/--
corrected determinant の平方は符号を消して exact `2^(2*strongPrecision)`。
-/
theorem correctedChristoffelWronskianNext_sq
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j) :
    correctedChristoffelWronskianNext D j ^ 2 =
      (2 : ℤ) ^ (2 * D.strongPrecision j) := by
  rcases correctedChristoffelWronskianNext_signed_strongPrecision W hjStart with
    hEven | hOdd
  · rw [hEven.2]
    rw [show (-((2 : ℤ) ^ D.strongPrecision j)) ^ 2 =
      ((2 : ℤ) ^ D.strongPrecision j) ^ 2 by ring]
    rw [← pow_mul]
    congr 1
    omega
  · rw [hOdd.2]
    rw [← pow_mul]
    congr 1
    omega

end ExternalArithmetic
end CSTMicro
end Collatz2
