import CollatzLean.Collatz3.Experimental2.NormalizationSlopeBridge
import CollatzLean.Collatz3.Experimental2.RationalMechanical
import CollatzLean.Collatz3.Experimental2.MechanicalRoofDerived

/-!
# Collatz3 Experimental2: carry word と balancedness

旧 Experimental の carry-word API を、新設計では

* `carryWord = c(n,1)`
* normalized roof の離散微分

として戻す。

carry word の balancedness は slope を使わず unit-carry だけから導く。
-/

namespace Collatz3
namespace Experimental2

/-- 一歩進むときの carry bit。 -/
def carryWord
    (β : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  roofCarry β n 1

/-- start `a` から長さ `r` の carry word weight。 -/
def carryWordWeight
    (β : ℕ → ℕ)
    (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ r =>
      carryWordWeight β a r + carryWord β (a + r)

namespace HasUnitCarry

/-- carry word の各 bit は `0` または `1`。 -/
theorem carryWord_eq_zero_or_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    carryWord β n = 0 ∨ carryWord β n = 1 :=
  U.carry_eq_zero_or_one n 1

/-- 任意区間の roof 増分は linear part と carry-word weight に exact 分解される。 -/
theorem beta_add_eq_linear_add_carryWordWeight
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ a r,
      β (a + r) = β a + r * β 1 + carryWordWeight β a r
  | a, 0 => by simp [carryWordWeight]
  | a, Nat.succ r => by
      have hPrev := U.beta_add_eq_linear_add_carryWordWeight a r
      have hStep := U.add_eq (a + r) 1
      calc
        β (a + Nat.succ r) = β ((a + r) + 1) := by congr 1
        _ = β (a + r) + β 1 + carryWord β (a + r) := by
          simpa [carryWord] using hStep
        _ = β a + (r + 1) * β 1 + carryWordWeight β a (r + 1) := by
          rw [hPrev]
          simp [carryWordWeight, Nat.add_mul]
          omega

/-- prefix carry weight は normalized roof そのもの。 -/
theorem normalizeRoof_eq_carryWordWeight_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    normalizeRoof β n = carryWordWeight β 0 n := by
  have hWord := U.beta_add_eq_linear_add_carryWordWeight 0 n
  have hNorm := U.eq_linear_add_normalizeRoof n
  simp [U.zero_eq] at hWord
  omega

/-- 同長 factor weight は prefix weight + 一個の block carry。 -/
theorem carryWordWeight_eq_prefix_add_carry
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a r : ℕ) :
    carryWordWeight β a r =
      carryWordWeight β 0 r + roofCarry β a r := by
  have hAtA := U.beta_add_eq_linear_add_carryWordWeight a r
  have hAtZero := U.beta_add_eq_linear_add_carryWordWeight 0 r
  have hAdd := U.add_eq a r
  simp [U.zero_eq] at hAtZero
  omega

/-- unit-carry word の balancedness。 -/
theorem carryWord_balanced
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b r : ℕ) :
    carryWordWeight β a r ≤ carryWordWeight β b r + 1 ∧
      carryWordWeight β b r ≤ carryWordWeight β a r + 1 := by
  have hA := U.carryWordWeight_eq_prefix_add_carry a r
  have hB := U.carryWordWeight_eq_prefix_add_carry b r
  have hCA := U.carry_le_one a r
  have hCB := U.carry_le_one b r
  omega

/-- factor weight は prefix と同じか、ちょうど1大きい。 -/
theorem carryWordWeight_eq_prefix_or_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a r : ℕ) :
    carryWordWeight β a r = carryWordWeight β 0 r ∨
      carryWordWeight β a r = carryWordWeight β 0 r + 1 := by
  have h := U.carryWordWeight_eq_prefix_add_carry a r
  rcases U.carry_eq_zero_or_one a r with h0 | h1 <;> omega

/-- direct roof 上では一歩 carry は `β(n+1) - (β(n)+β(1))`。 -/
theorem carryWord_eq_roof_succ_sub
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    carryWord β n = β (n + 1) - (β n + β 1) := by
  have h := U.add_eq n 1
  unfold carryWord
  omega

/--
一歩 carry は normalized roof の離散微分そのもの。

`w(n) = Nβ(n+1) - Nβ(n)`。
-/
theorem carryWord_eq_normalizeRoof_succ_sub
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    carryWord β n =
      normalizeRoof β (n + 1) - normalizeRoof β n := by
  have h := U.normalizeRoof_add_eq n 1
  have hOne : normalizeRoof β 1 = 0 := by simp [normalizeRoof]
  have hEq :
      normalizeRoof β (n + 1) =
        normalizeRoof β n + carryWord β n := by
    simpa [carryWord, hOne, Nat.add_assoc] using h
  omega

/-- normalized roof が lower mechanical なら carry word は floor 差分になる。 -/
theorem carryWord_eq_normalizedFloorDiff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof (normalizeRoof β) ρ)
    (n : ℕ) :
    carryWord β n =
      ⌊((n + 1 : ℕ) : ℝ) * ρ⌋₊ -
        ⌊(n : ℝ) * ρ⌋₊ := by
  rw [U.carryWord_eq_normalizeRoof_succ_sub]
  rw [M.eq_natFloor' (n + 1), M.eq_natFloor' n]

/-- direct lower mechanical roof では carry は3つの floor の additive defect。 -/
theorem carryWord_eq_directLowerFloorDefect
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (n : ℕ) :
    carryWord β n =
      ⌊((n + 1 : ℕ) : ℝ) * σ⌋₊ -
        (⌊(n : ℝ) * σ⌋₊ + ⌊σ⌋₊) := by
  rw [U.carryWord_eq_roof_succ_sub]
  rw [M.eq_natFloor' (n + 1), M.eq_natFloor' n, M.eq_natFloor' 1]
  simp

/-- normalized rational lower 型では carry word も Nat 除算差分で exact。 -/
theorem carryWord_eq_normalizedRationalLowerDiff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope (normalizeRoof β) p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : normalizeRoof β q = p)
    (n : ℕ) :
    carryWord β n =
      lowerRationalRoof p q (n + 1) - lowerRationalRoof p q n := by
  have Ures := U.normalizeRoof_hasUnitCarry
  rw [U.carryWord_eq_normalizeRoof_succ_sub]
  rw [Ures.rationalLower_eq_closedForm S hCoprime hLower (n + 1)]
  rw [Ures.rationalLower_eq_closedForm S hCoprime hLower n]

/-- normalized rational upper 型でも Nat 除算差分で exact。 -/
theorem carryWord_eq_normalizedRationalUpperDiff
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope (normalizeRoof β) p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : normalizeRoof β q + 1 = p)
    (n : ℕ) :
    carryWord β n =
      upperRationalRoof p q (n + 1) - upperRationalRoof p q n := by
  have Ures := U.normalizeRoof_hasUnitCarry
  rw [U.carryWord_eq_normalizeRoof_succ_sub]
  rw [Ures.rationalUpper_eq_closedForm S hCoprime hUpper (n + 1)]
  rw [Ures.rationalUpper_eq_closedForm S hCoprime hUpper n]

end HasUnitCarry
end Experimental2
end Collatz3
