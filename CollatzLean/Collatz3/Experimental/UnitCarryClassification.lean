import CollatzLean.Collatz3.Experimental.CarryWordBalance
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Collatz3 experimental: unit-carry roof の slope 分類

carry word の balancedness の次に、roof residual

`γ(n) = β(n) - n*β(1)`

を slope `ρ` に対して分類する。

全面書き換え前の実験なので、解析学的な極限の存在そのものを fat な structure に保存しない。
代わりに Fekete / homogenization が最終的に与える有限 exact window

`γ(n) ≤ nρ ≤ γ(n)+1`

だけを `IsHomogenizedSlope` として薄く切り出す。

そこから

* integral multiple が無い slope では `γ(n)` が `nρ` の floor に一意
* rational slope `p/q` では非境界点は strict window
* 分母境界では lower / upper の二型しかなく、その型は全正倍数へ伝播

を導く。
-/

namespace Collatz3
namespace Experimental

/--
`k` が実数 `x` の Nat-valued floor であることを、floor API に依存せず区間で表す。
-/
def IsNatFloor (k : ℕ) (x : ℝ) : Prop :=
  (k : ℝ) ≤ x ∧ x < (k : ℝ) + 1

/--
homogenized slope の有限 exact certificate。

`γ(n)` と `nρ` の距離が一単位幅の同じ整数区間に入る。
解析的な slope existence は後段でこの predicate を構成すればよい。
-/
def IsHomogenizedSlope
    (β : ℕ → ℕ)
    (ρ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (roofResidual β n : ℝ) ≤ (n : ℝ) * ρ ∧
      (n : ℝ) * ρ ≤ (roofResidual β n : ℝ) + 1

/--
正整数倍 `nρ` が整数境界に一度も乗らないこと。
実数 `ρ` が irrational なら満たすべき、今回の証明に必要な最小 arithmetic 条件。
-/
def HasNoIntegralMultiple (ρ : ℝ) : Prop :=
  ∀ n k : ℕ, 0 < n →
    (n : ℝ) * ρ ≠ (k : ℝ)

/--
rational slope `p/q` の整数演算版 certificate。
Real division を使わず、window を `q` 倍して保持する。
-/
def IsScaledRationalSlope
    (β : ℕ → ℕ)
    (p q : ℕ) : Prop :=
  0 < q ∧
    ∀ n : ℕ, 0 < n →
      q * roofResidual β n ≤ n * p ∧
        n * p ≤ q * (roofResidual β n + 1)

namespace HasUnitCarry

/-- homogenized slope は unit interval `[0,1]` に入る。 -/
theorem homogenizedSlope_mem_unitInterval
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (S : IsHomogenizedSlope β ρ) :
    0 ≤ ρ ∧ ρ ≤ 1 := by
  have h := S 1 (by omega)
  simp only [roofResidual, one_mul, tsub_self, Nat.cast_zero, Nat.cast_one, zero_add] at h
  exact h

/--
integer boundary が無い slope では residual は `nρ` の exact floor。

`IsNatFloor (γ n) (nρ)` という形なので Mathlib の floor 実装詳細に依存しない。
-/
theorem residual_isNatFloor_of_noIntegralMultiple
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (S : IsHomogenizedSlope β ρ)
    (H : HasNoIntegralMultiple ρ)
    {n : ℕ}
    (hn : 0 < n) :
    IsNatFloor (roofResidual β n) ((n : ℝ) * ρ) := by
  have hWindow := S n hn
  refine ⟨hWindow.1, ?_⟩
  rcases lt_or_eq_of_le hWindow.2 with hLt | hEq
  · exact hLt
  · exfalso
    have hIntegral :
        (n : ℝ) * ρ = ((roofResidual β n + 1 : ℕ) : ℝ) := by
      norm_num at hEq ⊢
      exact hEq
    exact H n (roofResidual β n + 1) hn hIntegral

/--
integer boundary が無い場合は lower side も strict。
したがって `nρ` は residual の真に内側にある。
-/
theorem residual_strict_window_of_noIntegralMultiple
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (S : IsHomogenizedSlope β ρ)
    (H : HasNoIntegralMultiple ρ)
    {n : ℕ}
    (hn : 0 < n) :
    (roofResidual β n : ℝ) < (n : ℝ) * ρ ∧
      (n : ℝ) * ρ < (roofResidual β n : ℝ) + 1 := by
  have hWindow := S n hn
  have hLowerNe :
      (n : ℝ) * ρ ≠ (roofResidual β n : ℝ) :=
    H n (roofResidual β n) hn
  have hUpperNe :
      (n : ℝ) * ρ ≠ ((roofResidual β n + 1 : ℕ) : ℝ) :=
    H n (roofResidual β n + 1) hn
  constructor
  · rcases lt_or_eq_of_le hWindow.1 with hLt | hEq
    · exact hLt
    · exfalso
      exact hLowerNe hEq.symm
  · rcases lt_or_eq_of_le hWindow.2 with hLt | hEq
    · exact hLt
    · exfalso
      apply hUpperNe
      norm_num at hEq ⊢
      exact hEq

/--
rational scaled window の非境界点では、両側が strict。
したがって residual は `np/q` の一意な整数 floor cell にいる。
-/
theorem rationalSlope_strictWindow_of_not_dvd
    {β : ℕ → ℕ}
    {p q n : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hn : 0 < n)
    (hNotDvd : ¬ q ∣ n * p) :
    q * roofResidual β n < n * p ∧
      n * p < q * (roofResidual β n + 1) := by
  have hWindow := S.2 n hn
  have hLeftNe : q * roofResidual β n ≠ n * p := by
    intro hEq
    apply hNotDvd
    exact ⟨roofResidual β n, hEq.symm⟩
  have hRightNe : n * p ≠ q * (roofResidual β n + 1) := by
    intro hEq
    apply hNotDvd
    exact ⟨roofResidual β n + 1, hEq⟩
  exact ⟨lt_of_le_of_ne hWindow.1 hLeftNe,
    lt_of_le_of_ne hWindow.2 hRightNe⟩

/--
分母 `q` 自身では residual は二型だけ:

* lower boundary: `γ(q)=p`
* upper boundary: `γ(q)+1=p`
-/
theorem rationalSlope_denominator_two_boundary_types
    {β : ℕ → ℕ}
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q) :
    roofResidual β q = p ∨
      roofResidual β q + 1 = p := by
  have hq := S.1
  have hWindow := S.2 q hq
  have hLe : roofResidual β q ≤ p := by
    nlinarith
  have hGe : p ≤ roofResidual β q + 1 := by
    nlinarith
  omega

/--
lower boundary 型 `γ(q)=p` は分母の全倍数へ exact に伝播する。
-/
theorem rationalSlope_lowerBoundary_propagates
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hAtQ : roofResidual β q = p) :
    ∀ k : ℕ,
      roofResidual β (k * q) = k * p
  | 0 => by
      simp [roofResidual, U.zero_eq]
  | Nat.succ k => by
      have hPrev :=
        U.rationalSlope_lowerBoundary_propagates S hAtQ k
      have hAdd := U.residual_add_eq (k * q) q
      have hWindow := S.2 ((k + 1) * q) (by
        have hq := S.1
        positivity)
      have hUpper :
          roofResidual β ((k + 1) * q) ≤ (k + 1) * p := by
        have hq := S.1
        nlinarith
      have hIndex :
          k * q + q = (k + 1) * q := by
        simp [Nat.add_mul]
      have hValueIndex :
          k * p + p = (k + 1) * p := by
        simp [Nat.add_mul]
      rw [hIndex, hPrev, hAtQ] at hAdd
      rw [hValueIndex] at hAdd
      have hEq :
          roofResidual β ((k + 1) * q) = (k + 1) * p := by
        omega
      simpa [Nat.succ_eq_add_one] using hEq

/--
upper boundary 型 `γ(q)+1=p` も混在せず、全正倍数で
`γ(kq)+1=kp` を保つ。
-/
theorem rationalSlope_upperBoundary_propagates
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (S : IsScaledRationalSlope β p q)
    (hAtQ : roofResidual β q + 1 = p) :
    ∀ k : ℕ, 0 < k →
      roofResidual β (k * q) + 1 = k * p := by
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
      induction k with
      | zero =>
          simpa using hAtQ
      | succ k ih =>
          have hPrev :
              roofResidual β ((k + 1) * q) + 1 = (k + 1) * p := by exact ih (by omega)
          have hAdd := U.residual_add_eq ((k + 1) * q) q
          have hCarryLe := U.carry_le_one ((k + 1) * q) q
          have hWindow := S.2 ((k + 2) * q) (by
            have hq := S.1
            positivity)
          have hLower :
              (k + 2) * p ≤ roofResidual β ((k + 2) * q) + 1 := by
            have hq := S.1
            nlinarith
          have hIndex : (k + 1) * q + q = (k + 2) * q := by
            calc
              (k + 1) * q + q =
                  (k + 1) * q + 1 * q := by simp
              _ = ((k + 1) + 1) * q := by
                  rw [← Nat.add_mul]
              _ = (k + 2) * q := by
                  simp [Nat.add_assoc]
          have hValueIndex :
              (k + 1) * p + p = (k + 2) * p := by
            calc
              (k + 1) * p + p =
                  (k + 1) * p + 1 * p := by simp
              _ = ((k + 1) + 1) * p := by
                  rw [← Nat.add_mul]
              _ = (k + 2) * p := by
                  simp [Nat.add_assoc]
          rw [hIndex] at hAdd
          have hUpper :
              roofResidual β ((k + 2) * q) + 1 ≤
                (k + 2) * p := by
            omega
          have hEq :
              roofResidual β ((k + 2) * q) + 1 =
                (k + 2) * p :=
            Nat.le_antisymm hUpper hLower
          simpa [Nat.add_assoc] using hEq

end HasUnitCarry
end Experimental
end Collatz3
