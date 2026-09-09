import CollatzLean.Collatz3.Experimental.ReducedRationalSlope

/-!
# Collatz3 experimental: rational lower / upper 型の全幅 closed form

既約 rational slope

`ρ = p/q`, `0 < q`, `Coprime p q`

では、`q ∣ n*p` と `q ∣ n` が同値になる。
したがって rational boundary は exactly `q` の倍数であり、
前段で得た lower / upper boundary propagation と非境界 strict window を
全ての `n` に対する一つの式へまとめられる。

lower 型:

`γ(n) = (n*p) / q`

upper 型:

`γ(n) = (n*p - 1) / q`

後者は `n*p/q` が整数のときだけ一つ下の整数を選ぶ convention を
Nat の除算だけで表したもの。
-/

namespace Collatz3
namespace Experimental

/-- rational lower 型の closed residual。 -/
def lowerRationalResidual
    (p q n : ℕ) : ℕ :=
  (n * p) / q

/-- rational upper 型の closed residual。`n=0` でも Nat subtraction により `0`。 -/
def upperRationalResidual
    (p q n : ℕ) : ℕ :=
  (n * p - 1) / q

/--
`k` が実数 `x` の upper mechanical cell に入ること。

lower floor cell `k ≤ x < k+1` に対し、こちらは
`k < x ≤ k+1`。
-/
def IsNatUpperCell (k : ℕ) (x : ℝ) : Prop :=
  (k : ℝ) < x ∧ x ≤ (k : ℝ) + 1

namespace HasUnitCarry

/--
lower boundary 型では、どの正幅 `n` でも upper side は strict。

非境界では既存 strict-window theorem、境界では `Coprime p q` により
`n = kq` と分かり、lower propagation と upper equality が衝突する。
-/
theorem rationalLower_strictUpper
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : roofResidual β q = p)
    (hn : 0 < n) :
    n * p < q * (roofResidual β n + 1) := by
  by_contra hNot
  have hWindow := S.2 n hn
  have hGe : q * (roofResidual β n + 1) ≤ n * p :=
    Nat.le_of_not_gt hNot
  have hEq :
      n * p = q * (roofResidual β n + 1) :=
    Nat.le_antisymm hWindow.2 hGe
  have hDvd : q ∣ n * p :=
    ⟨roofResidual β n + 1, hEq⟩
  have hqn : q ∣ n :=
    (dvd_mul_right_iff_dvd_of_coprime hCoprime).1 hDvd
  rcases hqn with ⟨k, hk⟩
  have hProp :=
    U.rationalSlope_lowerBoundary_propagates S hLower k
  have hRes : roofResidual β n = k * p := by
    rw [hk]
    simpa [Nat.mul_comm] using hProp
  have hEq' : q * (k * p) = q * (k * p + 1) := by
    have hEqN := hEq
    rw [hRes] at hEqN
    rw [hk] at hEqN
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hEqN
  have hImpossible : k * p = k * p + 1 :=
    Nat.mul_left_cancel S.1 hEq'
  omega

/--
upper boundary 型では、どの正幅 `n` でも lower side は strict。

境界なら `n = kq`。upper propagation は `γ(kq)+1=kp` を与えるため、
`qγ(n)=np` とは両立しない。
-/
theorem rationalUpper_strictLower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : roofResidual β q + 1 = p)
    (hn : 0 < n) :
    q * roofResidual β n < n * p := by
  by_contra hNot
  have hWindow := S.2 n hn
  have hLe : n * p ≤ q * roofResidual β n :=
    Nat.le_of_not_gt hNot
  have hEq :
      q * roofResidual β n = n * p :=
    Nat.le_antisymm hWindow.1 hLe
  have hDvd : q ∣ n * p :=
    ⟨roofResidual β n, hEq.symm⟩
  have hqn : q ∣ n :=
    (dvd_mul_right_iff_dvd_of_coprime hCoprime).1 hDvd
  rcases hqn with ⟨k, hk⟩
  have hkPos : 0 < k := by
    by_contra hkNotPos
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hkNotPos
    subst k
    simp at hk
    omega
  have hProp :=
    U.rationalSlope_upperBoundary_propagates S hUpper k hkPos
  have hEq' :
      q * roofResidual β n = q * (k * p) := by
    calc
      q * roofResidual β n = n * p := hEq
      _ = q * (k * p) := by
        rw [hk]
        simp [Nat.mul_assoc]
  have hRes : roofResidual β n = k * p :=
    Nat.mul_left_cancel S.1 hEq'
  have hPropN : roofResidual β n + 1 = k * p := by
    rw [hk]
    simpa [Nat.mul_comm] using hProp
  omega

/--
lower rational 型の residual は全 `n` で exact に `(n*p)/q`。
-/
theorem rationalLower_residual_eq_div
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : roofResidual β q = p) :
    ∀ n : ℕ,
      roofResidual β n = lowerRationalResidual p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [lowerRationalResidual, U.roofResidual_zero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict :=
      U.rationalLower_strictUpper S hCoprime hLower hnPos
    unfold lowerRationalResidual
    symm
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using hWindow.1
    · simpa [Nat.mul_comm] using hStrict

/--
upper rational 型の residual は全 `n` で exact に `(n*p - 1)/q`。
-/
theorem rationalUpper_residual_eq_sub_one_div
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : roofResidual β q + 1 = p) :
    ∀ n : ℕ,
      roofResidual β n = upperRationalResidual p q n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [upperRationalResidual, U.roofResidual_zero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hWindow := S.2 n hnPos
    have hStrict :=
      U.rationalUpper_strictLower S hCoprime hUpper hnPos
    have hLo :
        roofResidual β n * q ≤ n * p - 1 := by
      have hStrict' : roofResidual β n * q < n * p := by
        simpa [Nat.mul_comm] using hStrict
      omega
    have hRightPos :
        0 < (roofResidual β n + 1) * q := by
      exact Nat.mul_pos (by omega) S.1
    have hHi :
        n * p - 1 < (roofResidual β n + 1) * q := by
      have hUpper' :
          n * p ≤ (roofResidual β n + 1) * q := by
        simpa [Nat.mul_comm] using hWindow.2
      omega
    unfold upperRationalResidual
    symm
    exact Nat.div_eq_of_lt_le hLo hHi

/--
lower rational 型は実数 slope `p/q` に対して通常の floor cell に入る。
-/
theorem rationalLower_isNatFloor
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hLower : roofResidual β q = p)
    (hn : 0 < n) :
    IsNatFloor
      (roofResidual β n)
      ((n : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast S.1
  have hWindow := S.2 n hn
  have hStrict :=
    U.rationalLower_strictUpper S hCoprime hLower hn
  have hFrac :
      (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
        ((n * p : ℕ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hFrac]
  constructor
  · apply (le_div_iff₀ hqR).2
    exact_mod_cast (show roofResidual β n * q ≤ n * p by
      simpa [Nat.mul_comm] using hWindow.1)
  · apply (div_lt_iff₀ hqR).2
    exact_mod_cast (show n * p < (roofResidual β n + 1) * q by
      simpa [Nat.mul_comm] using hStrict)

/--
upper rational 型は実数 slope `p/q` に対して upper cell `γ < nρ ≤ γ+1` に入る。
-/
theorem rationalUpper_isNatUpperCell
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hCoprime : Nat.Coprime p q)
    (hUpper : roofResidual β q + 1 = p)
    (hn : 0 < n) :
    IsNatUpperCell
      (roofResidual β n)
      ((n : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast S.1
  have hWindow := S.2 n hn
  have hStrict :=
    U.rationalUpper_strictLower S hCoprime hUpper hn
  have hFrac :
      (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
        ((n * p : ℕ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hFrac]
  constructor
  · apply (lt_div_iff₀ hqR).2
    exact_mod_cast (show roofResidual β n * q < n * p by
      simpa [Nat.mul_comm] using hStrict)
  · apply (div_le_iff₀ hqR).2
    exact_mod_cast (show n * p ≤ (roofResidual β n + 1) * q by
      simpa [Nat.mul_comm] using hWindow.2)

/--
canonical slope が rational 側なら、既約 `p/q` が自動抽出され、
residual 全体は lower closed form または upper closed form のどちらか一方に入る。
-/
theorem exists_reduced_rational_closedForm_of_not_irrational
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hNotIrr : ¬ Irrational (residualSlope β)) :
    ∃ p q : ℕ,
      0 < q ∧
        p ≤ q ∧
          Nat.Coprime p q ∧
            residualSlope β =
              (p : ℝ) / (q : ℝ) ∧
              (
                (∀ n : ℕ,
                  roofResidual β n = lowerRationalResidual p q n) ∨
                (∀ n : ℕ,
                  roofResidual β n = upperRationalResidual p q n)
              ) := by
  obtain ⟨p, q, hq, hpq, hCoprime, hSlope, S⟩ :=
    U.exists_reduced_scaledRationalSlope_of_not_irrational hNotIrr
  refine ⟨p, q, hq, hpq, hCoprime, hSlope, ?_⟩
  rcases rationalSlope_denominator_two_boundary_types S with hLower | hUpper
  · left
    exact U.rationalLower_residual_eq_div S hCoprime hLower
  · right
    exact U.rationalUpper_residual_eq_sub_one_div S hCoprime hUpper

end HasUnitCarry
end Experimental
end Collatz3
