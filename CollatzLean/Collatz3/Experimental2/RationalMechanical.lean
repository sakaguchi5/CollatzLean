import CollatzLean.Collatz3.Experimental2.CarryCore
import CollatzLean.Collatz3.Experimental2.SlopeWindow
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: rational mechanical roof

generic slope は `[0,1]` に正規化しないため、`p ≤ q` は要求しない。

既約 `p/q` に対して boundary が exactly `q` の倍数であること、
lower / upper の全幅 closed form を証明する。
-/

namespace Collatz3
namespace Experimental2

def IsScaledRationalSlope
    (β : ℕ → ℕ)
    (p q : ℕ) : Prop :=
  0 < q ∧
    ∀ n : ℕ, 0 < n →
      q * β n ≤ n * p ∧
        n * p ≤ q * (β n + 1)

def lowerRationalRoof (p q n : ℕ) : ℕ :=
  (n * p) / q

def upperRationalRoof (p q n : ℕ) : ℕ :=
  (n * p - 1) / q

/-- roof slope `p/q` を整数演算の scaled window に降ろす。 -/
theorem roofSlope_to_scaledRational
    {β : ℕ → ℕ}
    {p q : ℕ}
    (hq : 0 < q)
    (S : IsRoofSlope β ((p : ℝ) / (q : ℝ))) :
    IsScaledRationalSlope β p q := by
  refine ⟨hq, ?_⟩
  intro n hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h := S n hn
  have hFrac :
      (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
        ((n * p : ℕ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hFrac] at h
  constructor
  · have hR :
        (β n : ℝ) * (q : ℝ) ≤ ((n * p : ℕ) : ℝ) :=
      (le_div_iff₀ hqR).mp h.1
    have hNat : β n * q ≤ n * p := by exact_mod_cast hR
    simpa [Nat.mul_comm] using hNat
  · have hR :
        ((n * p : ℕ) : ℝ) ≤ ((β n : ℝ) + 1) * (q : ℝ) :=
      (div_le_iff₀ hqR).mp h.2
    have hNat : n * p ≤ (β n + 1) * q := by exact_mod_cast hR
    simpa [Nat.mul_comm] using hNat

/-- 非無理な非負実数は既約自然数比で表せる。 -/
theorem exists_reduced_nat_ratio_of_not_irrational_nonneg
    {σ : ℝ}
    (hNotIrr : ¬ Irrational σ)
    (hNonneg : 0 ≤ σ) :
    ∃ p q : ℕ,
      0 < q ∧ Nat.Coprime p q ∧
        σ = (p : ℝ) / (q : ℝ) := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hNotIrr
  have hrNonnegReal : (0 : ℝ) ≤ (r : ℝ) := by
    rw [← hr]
    exact hNonneg
  have hrNonnegRat : (0 : ℚ) ≤ r := by
    exact_mod_cast hrNonnegReal
  let s : ℚ≥0 := ⟨r, hrNonnegRat⟩
  refine ⟨s.num, s.den, s.den_pos, s.coprime_num_den, ?_⟩
  calc
    σ = (r : ℝ) := hr
    _ = (s : ℝ) := by
      symm
      simp only [NNRat.cast_mk, s]
    _ = (s.num : ℝ) / (s.den : ℝ) := by
      rw [NNRat.cast_def]

theorem scaledBoundary_dvd_index_iff_of_coprime
    {p q n : ℕ}
    (hCoprime : Nat.Coprime p q) :
    q ∣ n * p ↔ q ∣ n := by
  constructor
  · intro h
    apply hCoprime.symm.dvd_of_dvd_mul_left
    simpa [Nat.mul_comm] using h
  · rintro ⟨k, rfl⟩
    exact ⟨k * p, by simp [Nat.mul_assoc]⟩

theorem rationalSlope_denominator_two_boundary_types
    {β : ℕ → ℕ}
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q) :
    β q = p ∨ β q + 1 = p := by
  have h := S.2 q S.1
  have hLe : β q ≤ p := by
    exact (Nat.le_of_mul_le_mul_left h.1) S.1
  have hGe : p ≤ β q + 1 := by
    exact (Nat.le_of_mul_le_mul_left h.2) S.1
  omega

namespace HasUnitCarry

theorem rationalSlope_lowerBoundary_propagates
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hAtQ : β q = p) :
    ∀ k : ℕ, β (k * q) = k * p
  | 0 => by
      simp [U.zero_eq]
  | Nat.succ k => by
      have hPrev :=
        U.rationalSlope_lowerBoundary_propagates S hAtQ k
      have hAdd :=
        U.add_eq (k * q) q
      have hq : 0 < q := S.1
      have hIndexPos : 0 < (k + 1) * q := by
        exact Nat.mul_pos (by omega) hq
      have hWindow :=
        S.2 ((k + 1) * q) hIndexPos
      have hScaled :
          q * β ((k + 1) * q) ≤
            q * ((k + 1) * p) := by
        calc
          q * β ((k + 1) * q)
              ≤ ((k + 1) * q) * p := hWindow.1
          _ = q * ((k + 1) * p) := by
              simp [ Nat.mul_comm, Nat.mul_left_comm]
      have hUpper :
          β ((k + 1) * q) ≤ (k + 1) * p := by
        exact (Nat.le_of_mul_le_mul_left hScaled) hq
      have hIndex :
          k * q + q = (k + 1) * q := by
        simp [Nat.add_mul]
      have hValueIndex :
          k * p + p = (k + 1) * p := by
        simp [Nat.add_mul]
      rw [hIndex, hPrev, hAtQ] at hAdd
      rw [hValueIndex] at hAdd
      have hEq :
          β ((k + 1) * q) = (k + 1) * p := by
        omega
      simpa [Nat.succ_eq_add_one] using hEq

theorem rationalSlope_upperBoundary_propagates
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hAtQ : β q + 1 = p) :
    ∀ k : ℕ, 0 < k → β (k * q) + 1 = k * p := by
  intro k hk
  cases k with
  | zero =>
      omega
  | succ k =>
      induction k with
      | zero =>
          simpa using hAtQ
      | succ k ih =>
          have hPrev :
              β ((k + 1) * q) + 1 = (k + 1) * p := by
            exact ih (by omega)
          have hAdd :=
            U.add_eq ((k + 1) * q) q
          have hCarryLe :=
            U.carry_le_one ((k + 1) * q) q
          have hq : 0 < q := S.1
          have hIndexPos : 0 < (k + 2) * q := by
            exact Nat.mul_pos (by omega) hq
          have hWindow :=
            S.2 ((k + 2) * q) hIndexPos
          have hScaled :
              q * ((k + 2) * p) ≤
                q * (β ((k + 2) * q) + 1) := by
            calc
              q * ((k + 2) * p) =
                  ((k + 2) * q) * p := by
                    simp [ Nat.mul_comm, Nat.mul_left_comm]
              _ ≤ q * (β ((k + 2) * q) + 1) :=
                hWindow.2
          have hLower :
              (k + 2) * p ≤ β ((k + 2) * q) + 1 := by
            exact (Nat.le_of_mul_le_mul_left hScaled) hq
          have hIndex :
              (k + 1) * q + q = (k + 2) * q := by
            calc
              (k + 1) * q + q =
                  (k + 1) * q + 1 * q := by
                    simp
              _ = ((k + 1) + 1) * q := by
                    rw [← Nat.add_mul]
              _ = (k + 2) * q := by
                    simp [Nat.add_assoc]
          rw [hIndex] at hAdd
          have hValueIndex :
              (k + 1) * p + p = (k + 2) * p := by
            simp [Nat.add_mul]
            ring
          have hUpper :
              β ((k + 2) * q) + 1 ≤ (k + 2) * p := by
            omega
          exact Nat.le_antisymm hUpper hLower

theorem rationalLower_strictUpper
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : β q = p)
    (hn : 0 < n) :
    n * p < q * (β n + 1) := by
  by_contra hNot
  have hWindow := S.2 n hn
  have hGe : q * (β n + 1) ≤ n * p := Nat.le_of_not_gt hNot
  have hEq : n * p = q * (β n + 1) :=
    Nat.le_antisymm hWindow.2 hGe
  have hqn : q ∣ n :=
    (scaledBoundary_dvd_index_iff_of_coprime hCoprime).1
      ⟨β n + 1, hEq⟩
  rcases hqn with ⟨k, hk⟩
  have hProp := U.rationalSlope_lowerBoundary_propagates S hLower k
  have hRes : β n = k * p := by
    rw [hk]
    simpa [Nat.mul_comm] using hProp
  rw [hRes, hk] at hEq
  have hEq' : q * (k * p) = q * (k * p + 1) := by
    simpa [Nat.mul_assoc] using hEq
  have hImpossible : k * p = k * p + 1 :=
    Nat.mul_left_cancel S.1 hEq'
  omega

theorem rationalUpper_strictLower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : β q + 1 = p)
    (hn : 0 < n) :
    q * β n < n * p := by
  by_contra hNot
  have hWindow := S.2 n hn
  have hLe : n * p ≤ q * β n := Nat.le_of_not_gt hNot
  have hEq : q * β n = n * p :=
    Nat.le_antisymm hWindow.1 hLe
  have hqn : q ∣ n :=
    (scaledBoundary_dvd_index_iff_of_coprime hCoprime).1
      ⟨β n, hEq.symm⟩
  rcases hqn with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp at hk
    omega
  have hProp := U.rationalSlope_upperBoundary_propagates S hUpper k hkPos
  have hRes : β n = k * p := by
    have hEq' : q * β n = q * (k * p) := by
      calc
        q * β n = n * p := hEq
        _ = q * (k * p) := by rw [hk]; simp [Nat.mul_assoc]
    exact Nat.mul_left_cancel S.1 hEq'
  have hPropN : β n + 1 = k * p := by
    rw [hk]
    simpa [Nat.mul_comm] using hProp
  omega

theorem rationalLower_eq_closedForm
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : β q = p) :
    ∀ n, β n = lowerRationalRoof p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [lowerRationalRoof, U.zero_eq]
  · have hnPos := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict := U.rationalLower_strictUpper S hCoprime hLower hnPos
    unfold lowerRationalRoof
    symm
    exact Nat.div_eq_of_lt_le
      (by simpa [Nat.mul_comm] using hWindow.1)
      (by simpa [Nat.mul_comm] using hStrict)

theorem rationalUpper_eq_closedForm
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : β q + 1 = p) :
    ∀ n, β n = upperRationalRoof p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [upperRationalRoof, U.zero_eq]
  · have hnPos := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict := U.rationalUpper_strictLower S hCoprime hUpper hnPos
    unfold upperRationalRoof
    symm
    apply Nat.div_eq_of_lt_le
    · have h : β n * q < n * p := by
        simpa [Nat.mul_comm] using hStrict
      omega
    · have h : n * p ≤ (β n + 1) * q := by
        simpa [Nat.mul_comm] using hWindow.2
      omega

end HasUnitCarry
end Experimental2
end Collatz3
