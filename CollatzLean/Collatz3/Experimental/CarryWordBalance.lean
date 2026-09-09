import CollatzLean.Collatz3.Experimental.CarryDefectRefinement

/-!
# Collatz3 experimental: carry word と balancedness

`HasUnitCarry β` から一歩 carry

`w(n) = c(n,1)`

を読む。

この binary word だけで roof の非線形成分を復元でき、
任意の同長区間に含まれる `1` の個数は高々 1 しか違わないことを示す。

これは Beatty / Sturmian を仮定せず、unit-carry 公理だけから出る。
-/

namespace Collatz3
namespace Experimental

/-- 一歩進むときの carry bit。 -/
def carryWord
    (β : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  roofCarry β n 1

/--
start `a` から長さ `r` の carry word weight。
List を原始 data にせず、有限再帰だけで数える。
-/
def carryWordWeight
    (β : ℕ → ℕ)
    (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ r =>
      carryWordWeight β a r + carryWord β (a + r)

/-- roof の整数線形成分 `n * β(1)` を除いた residual。 -/
def roofResidual
    (β : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  β n - n * β 1

namespace HasUnitCarry

/-- carry word の各 bit は 0 または 1。 -/
theorem carryWord_eq_zero_or_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    carryWord β n = 0 ∨ carryWord β n = 1 := by
  exact U.carry_eq_zero_or_one n 1

/-- `n * β(1)` は常に `β(n)` 以下。residual が Nat subtraction で lossless になる。 -/
theorem linearPart_le
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    n * β 1 ≤ β n := by
  have h := U.mul_lower n 1
  simpa using h

/-- roof は linear part + residual に exact 分解できる。 -/
theorem beta_eq_linear_add_residual
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    β n = n * β 1 + roofResidual β n := by
  have hLe := U.linearPart_le n
  unfold roofResidual
  omega

/--
任意 start の長さ `r` 区間について、roof 増分は
`r * β(1) + carryWordWeight` に exact 分解される。
-/
theorem beta_add_eq_linear_add_carryWordWeight
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ (a r : ℕ),
      β (a + r) =
        β a + r * β 1 + carryWordWeight β a r
  | a, 0 => by
      simp [carryWordWeight]
  | a, Nat.succ r => by
      have hPrev :=
        U.beta_add_eq_linear_add_carryWordWeight a r
      have hStep := U.add_eq (a + r) 1
      calc
        β (a + Nat.succ r) = β ((a + r) + 1) := by
          congr 1
        _ = β (a + r) + β 1 + carryWord β (a + r) := by
          simpa [carryWord] using hStep
        _ = β a + (r + 1) * β 1 + carryWordWeight β a (r + 1) := by
          rw [hPrev]
          simp [carryWordWeight, Nat.add_mul]
          omega

/--
prefix carry word weight は roof residual そのもの。

`β(n) = n*β(1) + weight(0,n)`。
-/
theorem roofResidual_eq_carryWordWeight_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (n : ℕ) :
    roofResidual β n = carryWordWeight β 0 n := by
  have hWord := U.beta_add_eq_linear_add_carryWordWeight 0 n
  have hZero := U.zero_eq
  have hResidual := U.beta_eq_linear_add_residual n
  simp [hZero] at hWord
  omega

/--
同じ長さ `r` の任意 factor weight は、prefix weight に `c(a,r)` を足したもの。

`weight(a,r) = weight(0,r) + c(a,r)`。
-/
theorem carryWordWeight_eq_prefix_add_carry
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a r : ℕ) :
    carryWordWeight β a r =
      carryWordWeight β 0 r + roofCarry β a r := by
  have hAtA := U.beta_add_eq_linear_add_carryWordWeight a r
  have hAtZero := U.beta_add_eq_linear_add_carryWordWeight 0 r
  have hZero := U.zero_eq
  have hAdd := U.add_eq a r
  simp [hZero] at hAtZero
  omega

/--
unit-carry word の balancedness。

同じ長さ `r` の二つの factor に含まれる `1` の個数は高々 1 しか違わない。
絶対値を導入せず、両向きの `≤ + 1` として表す。
-/
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

/--
factor が prefix より重いかどうかは carry 一個で exact に決まる。
-/
theorem carryWordWeight_eq_prefix_or_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a r : ℕ) :
    carryWordWeight β a r = carryWordWeight β 0 r ∨
      carryWordWeight β a r = carryWordWeight β 0 r + 1 := by
  have hExact := U.carryWordWeight_eq_prefix_add_carry a r
  rcases U.carry_eq_zero_or_one a r with hZero | hOne
  · left
    omega
  · right
    omega

/-- residual 自体も同じ carry cocycle を持つ。 -/
theorem residual_add_eq
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofResidual β (a + b) =
      roofResidual β a + roofResidual β b + roofCarry β a b := by
  have hA := U.beta_eq_linear_add_residual a
  have hB := U.beta_eq_linear_add_residual b
  have hAB := U.beta_eq_linear_add_residual (a + b)
  have hAdd := U.add_eq a b
  simp only [Nat.add_mul] at hAB
  omega

/-- residual at 0 is 0。 -/
@[simp] theorem roofResidual_zero
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    roofResidual β 0 = 0 := by
  simp [roofResidual, U.zero_eq]

/-- residual at 1 is 0。 -/
@[simp] theorem roofResidual_one
    {β : ℕ → ℕ} :
    roofResidual β 1 = 0 := by
  simp [roofResidual]

end HasUnitCarry
end Experimental
end Collatz3
