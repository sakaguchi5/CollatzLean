import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33MorphismStage

/-!
# BHZ phase digit uniqueness

BHZ Proposition 3.3 は arbitrary な digit packet ではなく、与えられた Sturmian
point に付随する Ostrowski digit sequence `(c_k)` に対して述べられる。

一方、project-facing interface `BHZCriticalProposition33WordFormula` は

  P : CriticalBHZPhasePacket s

を任意に量化している。従って published theorem をそこへ安全に輸送する前に、
同じ integer phase `s` を表す `BHZCriticalPhaseExpansion` の digit list が一意である
ことを証明しておく必要がある。

各 step では

  s = rem + d * q_K,    rem < q_K

なので、`d = s / q_K` と `rem = s % q_K` が強制される。従って expansion の
構成証明が違っても digit list は同じである。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace BHZCriticalPhaseExpansion

/--
`rem < q` かつ `s = rem + d*q` なら quotient は exact に `d`。
-/
private theorem quotient_eq_of_decomp
    {s rem d q : ℕ}
    (hq : 0 < q)
    (hrem : rem < q)
    (hdec : s = rem + d * q) :
    s / q = d := by
  have hLower : d * q ≤ s := by
    rw [hdec]
    omega
  have hUpper : s < (d + 1) * q := by
    rw [hdec]
    nlinarith
  have hDLe : d ≤ s / q :=
    (Nat.le_div_iff_mul_le hq).2 hLower
  have hDivLt : s / q < d + 1 :=
    (Nat.div_lt_iff_lt_mul hq).2 hUpper
  omega

theorem digitsHigh_unique
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    ∀ F : BHZCriticalPhaseExpansion K s,
      E.digitsHigh = F.digitsHigh := by
  induction E with
  | base s hBound =>
      intro F
      cases F with
      | base s' hBound' =>
          rfl
      | @step _ s' rem' d' lower' hBound' hDec' hDigit' hMax' =>
          have hImpossible := lower'.top_ge_two
          omega
  | @step K s rem d lower hBound hDec hDigit hMax ih =>
      intro F
      cases F with
      | base s' hBound' =>
          have hImpossible := lower.top_ge_two
          omega
      | @step _ _ rem' d' lower' hBound' hDec' hDigit' hMax' =>
          have hq : 0 < criticalBHZq K := by
            unfold criticalBHZq
            exact criticalPowerP_pos (by omega)
          have hrem : rem < criticalBHZq K := lower.bound
          have hrem' : rem' < criticalBHZq K := lower'.bound
          have hd : s / criticalBHZq K = d :=
            quotient_eq_of_decomp hq hrem hDec
          have hd' : s / criticalBHZq K = d' :=
            quotient_eq_of_decomp hq hrem' hDec'
          have hdd : d = d' :=
            hd.symm.trans hd'
          have hEq :
              rem + d * criticalBHZq K =
                rem' + d * criticalBHZq K := by
            calc
              rem + d * criticalBHZq K
                  = s := hDec.symm
              _ = rem' + d' * criticalBHZq K := hDec'
              _ = rem' + d * criticalBHZq K := by
                    rw [hdd]
          have hrr : rem = rem' :=
            Nat.add_right_cancel hEq
          subst rem'
          simp only [digitsHigh]
          rw [hdd]
          rw [ih lower']

/-- 同じ phase expansion の digit accessor も pointwise に一意。 -/
theorem digit_unique
    {K s : ℕ}
    (E F : BHZCriticalPhaseExpansion K s)
    (k : ℕ) :
    E.digit k = F.digit k := by
  unfold digit
  rw [E.digitsHigh_unique F]

end BHZCriticalPhaseExpansion

namespace CriticalBHZPhasePacket

/-- 同じ integer phase `s` を持つ packet は全 BHZ digits が一致する。 -/
theorem digit_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    P.digit k = Q.digit k := by
  unfold CriticalBHZPhasePacket.digit
  exact P.expansion.digit_unique Q.expansion k

/-- 任意 packet の digit は canonical packet の digit と一致する。 -/
theorem digit_eq_canonical
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    P.digit k =
      (CriticalBHZPhasePacket.canonical s).digit k :=
  P.digit_eq_of_same_phase (CriticalBHZPhasePacket.canonical s) k

end CriticalBHZPhasePacket

/-- residual budget は packet の構成証明に依存しない。 -/
theorem bhzCriticalResidualBudget_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalResidualBudget P k =
      bhzCriticalResidualBudget Q k := by
  classical
  unfold bhzCriticalResidualBudget
  apply Finset.sum_congr rfl
  intro j hj
  rw [P.digit_eq_of_same_phase Q j]

/-- next-max indicator も packet の構成証明に依存しない。 -/
theorem bhzCriticalNextMaxIndicator_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalNextMaxIndicator P k =
      bhzCriticalNextMaxIndicator Q k := by
  unfold bhzCriticalNextMaxIndicator
  rw [P.digit_eq_of_same_phase Q (k + 2)]

/-- standard Prop.3.3 numerator は phase `s` だけで決まる。 -/
theorem bhzCriticalStandardPowerNumerator_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalStandardPowerNumerator P k =
      bhzCriticalStandardPowerNumerator Q k := by
  unfold bhzCriticalStandardPowerNumerator
  rw [
    bhzCriticalNextMaxIndicator_eq_of_same_phase P Q k,
    bhzCriticalResidualBudget_eq_of_same_phase P Q (k + 1)
  ]

/-- semistandard root は phase `s` だけで決まる。 -/
theorem bhzCriticalSemistandardRoot_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalSemistandardRoot P k =
      bhzCriticalSemistandardRoot Q k := by
  unfold bhzCriticalSemistandardRoot
  rw [P.digit_eq_of_same_phase Q k]

/-- semistandard canonical word は phase `s` だけで決まる。 -/
theorem bhzCriticalSemistandardWord_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalSemistandardWord P k =
      bhzCriticalSemistandardWord Q k := by
  rcases k with _ | k
  · rfl
  simp only [bhzCriticalSemistandardWord]
  rw [P.digit_eq_of_same_phase Q (k + 1)]

/-- semistandard Prop.3.3 numerator は phase `s` だけで決まる。 -/
theorem bhzCriticalSemistandardPowerNumerator_eq_of_same_phase
    {s : ℕ}
    (P Q : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalSemistandardPowerNumerator P k =
      bhzCriticalSemistandardPowerNumerator Q k := by
  unfold bhzCriticalSemistandardPowerNumerator
  rw [
    bhzCriticalSemistandardRoot_eq_of_same_phase P Q k,
    bhzCriticalResidualBudget_eq_of_same_phase P Q k
  ]

end ExternalArithmetic
end CSTMicro
end Collatz2
