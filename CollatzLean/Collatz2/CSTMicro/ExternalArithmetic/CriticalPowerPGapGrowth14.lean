import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinLinearForm14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

/-!
# Actual P-scale gap growth: degree 14

既存 Rhin theorem

  Q_(j+1) <= 2 * Q_j^14

を、Sturmian square root の長さ座標 `P_j` に移す。

まず actual continued-fraction recurrence の P/Q 両座標が同じ positive coefficient を
持つことから

  Q_j <= 2 * P_j      (j >= 2)

を内部証明する。すると

  P_(j+1)
    <= Q_(j+1)
    <= 2 Q_j^14
    <= 2 (2 P_j)^14
    = 32768 P_j^14.

また `P_j` は index 2 以降 strict increasing かつ cofinal なので、任意 `N>=2` を
唯一性を要求せず consecutive P-band のどこかに配置できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- index 2 以降、P-coordinate は weak monotone。 -/
theorem criticalPowerP_mono_from_two
    {i j : ℕ}
    (hi : 2 ≤ i)
    (hij : i ≤ j) :
    criticalPowerP i ≤ criticalPowerP j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hStep0 :=
        criticalPowerP_strict_succ
          (r := i + d) (by omega)
      have hStep :
          criticalPowerP (i + d) ≤
            criticalPowerP (i + (d + 1)) := by
        have := le_of_lt hStep0
        simpa [Nat.add_assoc] using this
      exact le_trans (ih (by omega)) hStep

/--
actual convergent の index 2 における cone inequality。
-/
theorem criticalPowerQ_le_two_mul_criticalPowerP_two :
    criticalPowerQ 2 ≤ 2 * criticalPowerP 2 := by
  norm_num [
    criticalPowerP,
    criticalPowerQ,
    criticalPowerConvergent,
    criticalInitialConvergent
  ]


/--
actual convergent の index 3 における cone inequality。
-/
theorem criticalPowerQ_le_two_mul_criticalPowerP_three :
    criticalPowerQ 3 ≤ 2 * criticalPowerP 3 := by
  norm_num [
    criticalPowerP,
    criticalPowerQ,
    criticalPowerConvergent,
    criticalInitialConvergent
  ]


/--
index 4 以降、P-coordinate は直前二項と actual partial quotient による
standard convergent recurrence を満たす。
-/
theorem criticalPowerP_recurrence_from_four
    {j : ℕ}
    (hj : 4 ≤ j) :
    criticalPowerP j =
      criticalPowerP (j - 2) +
        actualCriticalPartialQuotient (j - 1) *
          criticalPowerP (j - 1) := by
  have hr : 2 ≤ j - 1 := by
    omega
  have hSpec :=
    actualCriticalPartialQuotient_spec hr
  simpa only [
    show j - 1 - 1 = j - 2 by omega,
    show (j - 1) + 1 = j by omega
  ] using hSpec.2.1


/--
index 4 以降、Q-coordinate は直前二項と actual partial quotient による
standard convergent recurrence を満たす。
-/
theorem criticalPowerQ_recurrence_from_four
    {j : ℕ}
    (hj : 4 ≤ j) :
    criticalPowerQ j =
      criticalPowerQ (j - 2) +
        actualCriticalPartialQuotient (j - 1) *
          criticalPowerQ (j - 1) := by
  have hr : 2 ≤ j - 1 := by
    omega
  have hSpec :=
    actualCriticalPartialQuotient_spec hr
  simpa only [
    show j - 1 - 1 = j - 2 by omega,
    show (j - 1) + 1 = j by omega
  ] using hSpec.2.2

/--
cone `Q ≤ 2 P` は、同じ非負係数による positive linear combination で保存される。
-/
theorem two_mul_cone_preserved_by_add_mul
    {P₀ P₁ Q₀ Q₁ a : ℕ}
    (h₀ : Q₀ ≤ 2 * P₀)
    (h₁ : Q₁ ≤ 2 * P₁) :
    Q₀ + a * Q₁ ≤
      2 * (P₀ + a * P₁) := by
  calc
    Q₀ + a * Q₁
        ≤ 2 * P₀ + a * (2 * P₁) := by
            exact Nat.add_le_add h₀
              (Nat.mul_le_mul_left a h₁)
    _ = 2 * (P₀ + a * P₁) := by
          ring

/--
index 4 以降では、直前二つの convergent が cone `Q ≤ 2P` に入っていれば、
次の convergent も同じ cone に入る。
-/
theorem criticalPowerQ_le_two_mul_criticalPowerP_step
    {j : ℕ}
    (hj : 4 ≤ j)
    (hPrev1 :
      criticalPowerQ (j - 1) ≤
        2 * criticalPowerP (j - 1))
    (hPrev2 :
      criticalPowerQ (j - 2) ≤
        2 * criticalPowerP (j - 2)) :
    criticalPowerQ j ≤
      2 * criticalPowerP j := by
  rw [
    criticalPowerQ_recurrence_from_four hj,
    criticalPowerP_recurrence_from_four hj
  ]
  exact two_mul_cone_preserved_by_add_mul
    hPrev2 hPrev1

/--
actual convergent は index 2 以降で `Q_j ≤ 2 P_j`。

初期 index 2,3 は explicit table。
index 4 以降では P/Q が同じ partial quotient recurrence を満たし、
cone `Q ≤ 2P` がその positive linear combination で保存される。
-/
theorem criticalPowerQ_le_two_mul_criticalPowerP
    {j : ℕ}
    (hj : 2 ≤ j) :
    criticalPowerQ j ≤ 2 * criticalPowerP j := by
  revert hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      by_cases hj2 : j = 2
      · subst j
        exact criticalPowerQ_le_two_mul_criticalPowerP_two
      by_cases hj3 : j = 3
      · subst j
        exact criticalPowerQ_le_two_mul_criticalPowerP_three
      have hj4 : 4 ≤ j := by
        omega
      apply criticalPowerQ_le_two_mul_criticalPowerP_step hj4
      · exact ih (j - 1) (by omega) (by omega)
      · exact ih (j - 2) (by omega) (by omega)


/-- Rhin の Q-growth を P-growth に移した degree-14 gap bound。 -/
theorem criticalPowerP_next_le_32768_mul_pow14
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalPowerP (j + 1) ≤
      32768 * criticalPowerP j ^ 14 := by
  have hPQNext :
      criticalPowerP (j + 1) ≤ criticalPowerQ (j + 1) :=
    criticalPowerP_le_Q (j + 1)
  have hQNext := R.actual_q_next_le (j := j) hj
  have hQP :
      criticalPowerQ j ≤ 2 * criticalPowerP j :=
    criticalPowerQ_le_two_mul_criticalPowerP (by omega)
  have hPow :
      criticalPowerQ j ^ 14 ≤
        (2 * criticalPowerP j) ^ 14 :=
    Nat.pow_le_pow_left hQP 14
  calc
    criticalPowerP (j + 1)
        ≤ criticalPowerQ (j + 1) := hPQNext
    _ ≤ 2 * criticalPowerQ j ^ 14 := hQNext
    _ ≤ 2 * (2 * criticalPowerP j) ^ 14 :=
      Nat.mul_le_mul_left 2 hPow
    _ = 32768 * criticalPowerP j ^ 14 := by
      rw [mul_pow]
      norm_num
      ring

/-- `P_2 = 1`。scale selection の左端用。 -/
theorem criticalPowerP_two_eq_one :
    criticalPowerP 2 = 1 := by
  norm_num [
    criticalPowerP,
    criticalPowerConvergent,
    criticalInitialConvergent
  ]

/--
任意 threshold `N>=2` は、index 2 以降の consecutive P-band

  P_j <= N < P_(j+1)

のどこかに入る。

cofinality は既存 `self_lt_criticalPowerP_add_three` を使う。
-/
theorem exists_criticalPowerP_band
    {N : ℕ}
    (hN : 2 ≤ N) :
    ∃ j : ℕ,
      2 ≤ j ∧
      criticalPowerP j ≤ N ∧
      N < criticalPowerP (j + 1) := by
  have hExists :
      ∃ k : ℕ,
        N < criticalPowerP (2 + k + 1) := by
    refine ⟨N, ?_⟩
    have h := self_lt_criticalPowerP_add_three N
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  let k : ℕ := Nat.find hExists
  let j : ℕ := 2 + k
  have hUpper0 :
      N < criticalPowerP (2 + k + 1) := by
    simpa [k] using Nat.find_spec hExists
  have hUpper :
      N < criticalPowerP (j + 1) := by
    simpa [j, Nat.add_assoc] using hUpper0
  have hLower : criticalPowerP j ≤ N := by
    by_cases hk0 : k = 0
    · simp [j, hk0, criticalPowerP_two_eq_one]
      omega
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      have hNot :
          ¬ N < criticalPowerP (2 + (k - 1) + 1) := by
        apply Nat.find_min hExists
        dsimp [k]
        omega
      have hIdx :
          2 + (k - 1) + 1 = j := by
        dsimp [j]
        omega
      rw [hIdx] at hNot
      exact Nat.le_of_not_gt hNot
  exact ⟨j, by dsimp [j]; omega, hLower, hUpper⟩

end ExternalArithmetic
end CSTMicro
end Collatz2
