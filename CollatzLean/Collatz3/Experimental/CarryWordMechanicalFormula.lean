import CollatzLean.Collatz3.Experimental.RationalMechanicalClosedForm
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Collatz3 experimental: carry word の exact mechanical formula

前段までで residual `γ` の closed form が得られた。
このファイルでは一歩 carry

`w(n) = roofCarry β n 1`

を residual の一階差として読み、そのまま mechanical word の式へ落とす。

無理 slope では

`w(n) = floor((n+1)ρ) - floor(nρ)`

rational lower / upper 型では、それぞれ Nat 除算だけの exact な差分式を得る。
-/

namespace Collatz3
namespace Experimental

/-- 無理数 slope 側で現れる lower mechanical bit。 -/
noncomputable def lowerMechanicalBit
    (ρ : ℝ)
    (n : ℕ) : ℕ :=
  ⌊((n + 1 : ℕ) : ℝ) * ρ⌋₊ -
    ⌊(n : ℝ) * ρ⌋₊

/-- rational lower 型の exact mechanical bit。 -/
def lowerRationalMechanicalBit
    (p q n : ℕ) : ℕ :=
  lowerRationalResidual p q (n + 1) -
    lowerRationalResidual p q n

/-- rational upper 型の exact mechanical bit。 -/
def upperRationalMechanicalBit
    (p q n : ℕ) : ℕ :=
  upperRationalResidual p q (n + 1) -
    upperRationalResidual p q n

namespace HasUnitCarry

/--
一歩 carry は residual の一階差そのもの。

`γ(n+1) = γ(n) + w(n)` を Nat subtraction の形で読み直す。
-/
theorem carryWord_eq_residual_succ_sub
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    carryWord β n =
      roofResidual β (n + 1) - roofResidual β n := by
  have hAdd := U.residual_add_eq n 1
  have hOne : roofResidual β 1 = 0 := by
    simp
  have hEq :
      roofResidual β (n + 1) =
        roofResidual β n + carryWord β n := by
    simpa [carryWord, hOne, Nat.add_assoc] using hAdd
  omega

/--
canonical residual slope が無理数なら、residual は Mathlib の `Nat.floor` と exact に一致する。

前段では floor API に依存しない `IsNatFloor` で保持していた情報を、
ここで初めて concrete floor formula に戻す。
-/
theorem residual_eq_natFloor_of_residualSlope_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hIrr : Irrational (residualSlope β))
    (n : ℕ) :
    roofResidual β n =
      ⌊(n : ℝ) * residualSlope β⌋₊ := by
  by_cases hn : n = 0
  · subst n
    simp [U.roofResidual_zero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hFloor :=
      U.residual_isNatFloor_of_residualSlope_irrational
        hIrr hnPos
    have hSlopeNonneg : 0 ≤ residualSlope β :=
      U.residualSlope_mem_unitInterval.1
    have hNonneg :
        0 ≤ (n : ℝ) * residualSlope β := by
      positivity
    symm
    exact (Nat.floor_eq_iff hNonneg).2 (by
      simpa [IsNatFloor] using hFloor)

/--
無理 canonical slope では carry word が exact に lower mechanical word になる。

`w(n) = floor((n+1)ρ) - floor(nρ)`。
-/
theorem carryWord_eq_lowerMechanicalBit_of_residualSlope_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hIrr : Irrational (residualSlope β))
    (n : ℕ) :
    carryWord β n =
      lowerMechanicalBit (residualSlope β) n := by
  rw [U.carryWord_eq_residual_succ_sub]
  rw [U.residual_eq_natFloor_of_residualSlope_irrational hIrr (n + 1)]
  rw [U.residual_eq_natFloor_of_residualSlope_irrational hIrr n]
  rfl

/-- rational lower 型では carry word も Nat 除算の closed form で exact に書ける。 -/
theorem carryWord_eq_lowerRationalMechanicalBit
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : roofResidual β q = p)
    (n : ℕ) :
    carryWord β n =
      lowerRationalMechanicalBit p q n := by
  rw [U.carryWord_eq_residual_succ_sub]
  rw [U.rationalLower_residual_eq_div S hCoprime hLower (n + 1)]
  rw [U.rationalLower_residual_eq_div S hCoprime hLower n]
  rfl

/-- rational upper 型でも carry word は Nat 除算の closed form で exact に書ける。 -/
theorem carryWord_eq_upperRationalMechanicalBit
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : roofResidual β q + 1 = p)
    (n : ℕ) :
    carryWord β n =
      upperRationalMechanicalBit p q n := by
  rw [U.carryWord_eq_residual_succ_sub]
  rw [U.rationalUpper_residual_eq_sub_one_div S hCoprime hUpper (n + 1)]
  rw [U.rationalUpper_residual_eq_sub_one_div S hCoprime hUpper n]
  rfl

/--
canonical slope だけから carry word の exact formula まで分類した短いまとめ。

無理数なら floor 差分、有理数なら既約 `p/q` の lower / upper 除算差分のどちらか。
-/
theorem carryWord_completeMechanicalTrichotomy
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    (
      Irrational (residualSlope β) ∧
        ∀ n : ℕ,
          carryWord β n =
            lowerMechanicalBit (residualSlope β) n
    ) ∨
    (
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            Nat.Coprime p q ∧
              residualSlope β =
                (p : ℝ) / (q : ℝ) ∧
              ∀ n : ℕ,
                carryWord β n =
                  lowerRationalMechanicalBit p q n
    ) ∨
    (
      ∃ p q : ℕ,
        0 < q ∧
          p ≤ q ∧
            Nat.Coprime p q ∧
              residualSlope β =
                (p : ℝ) / (q : ℝ) ∧
              ∀ n : ℕ,
                carryWord β n =
                  upperRationalMechanicalBit p q n
    ) := by
  classical
  by_cases hIrr : Irrational (residualSlope β)
  · left
    refine ⟨hIrr, ?_⟩
    intro n
    exact
      U.carryWord_eq_lowerMechanicalBit_of_residualSlope_irrational
        hIrr n
  · right
    obtain ⟨p, q, hq, hpq, hCoprime, hSlope, S⟩ :=
      U.exists_reduced_scaledRationalSlope_of_not_irrational hIrr
    rcases rationalSlope_denominator_two_boundary_types S with hLower | hUpper
    · left
      refine ⟨p, q, hq, hpq, hCoprime, hSlope, ?_⟩
      intro n
      exact U.carryWord_eq_lowerRationalMechanicalBit
        S hCoprime hLower n
    · right
      refine ⟨p, q, hq, hpq, hCoprime, hSlope, ?_⟩
      intro n
      exact U.carryWord_eq_upperRationalMechanicalBit
        S hCoprime hUpper n

end HasUnitCarry
end Experimental
end Collatz3
