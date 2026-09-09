import CollatzLean.Collatz3.Experimental.IrrationalSlopeBridge

/-!
# Collatz3 experimental: Real slope window から scaled rational window への bridge

`IsHomogenizedSlope β (p/q)` を、既存の整数演算だけの
`IsScaledRationalSlope β p q` へ輸送する。

中心 bridge は単なる正分母による不等式の分母払いなので、
`HasUnitCarry` は不要。
`HasUnitCarry` は canonical slope `residualSlope β` を供給する corollary 側でのみ使う。
-/

namespace Collatz3
namespace Experimental

/--
Real-valued homogenized window の slope が `p/q` なら、
同じ情報を exact に Nat の scaled window として持てる。

`γ(n) ≤ n(p/q) ≤ γ(n)+1`

を正の `q` 倍して

`q*γ(n) ≤ n*p ≤ q*(γ(n)+1)`

へ変換する。
-/
theorem homogenizedSlope_to_scaledRational
    {β : ℕ → ℕ}
    {p q : ℕ}
    (hq : 0 < q)
    (S : IsHomogenizedSlope β ((p : ℝ) / (q : ℝ))) :
    IsScaledRationalSlope β p q := by
  refine ⟨hq, ?_⟩
  intro n hn
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hWindow := S n hn
  have hFrac :
      (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
        ((n * p : ℕ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  rw [hFrac] at hWindow
  have hLowerR :
      (roofResidual β n : ℝ) * (q : ℝ) ≤
        ((n * p : ℕ) : ℝ) := by
    exact (le_div_iff₀ hqR).mp hWindow.1
  have hUpperR :
      ((n * p : ℕ) : ℝ) ≤
        ((roofResidual β n : ℝ) + 1) * (q : ℝ) := by
    exact (div_le_iff₀ hqR).mp hWindow.2
  constructor
  · have hLowerNat :
        roofResidual β n * q ≤ n * p := by
      exact_mod_cast hLowerR
    simpa [Nat.mul_comm] using hLowerNat
  · have hUpperNat :
        n * p ≤ (roofResidual β n + 1) * q := by
      exact_mod_cast hUpperR
    simpa [Nat.mul_comm] using hUpperNat

namespace HasUnitCarry

/--
canonical residual slope が `p/q` と一致するなら、
その slope window は整数演算だけの `IsScaledRationalSlope` に降りる。
-/
theorem residualSlope_scaledRational_of_eq_div
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (hq : 0 < q)
    (hSlope : residualSlope β = (p : ℝ) / (q : ℝ)) :
    IsScaledRationalSlope β p q := by
  apply homogenizedSlope_to_scaledRational hq
  rw [← hSlope]
  exact U.residualSlope_isHomogenizedSlope

/--
canonical slope が `p/q` なら、分母 `q` で residual は lower/upper boundary の二型だけになる。
-/
theorem residualSlope_rational_denominator_two_boundary_types
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q : ℕ}
    (hq : 0 < q)
    (hSlope : residualSlope β = (p : ℝ) / (q : ℝ)) :
    roofResidual β q = p ∨
      roofResidual β q + 1 = p := by
  have Sscaled :=
    U.residualSlope_scaledRational_of_eq_div hq hSlope
  exact rationalSlope_denominator_two_boundary_types Sscaled

/--
canonical slope が `p/q` で、`q ∤ n*p` なら residual window は strict。
Real division を下流へ持ち込まず、整数演算だけで得る。
-/
theorem residualSlope_rational_strictWindow_of_not_dvd
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {p q n : ℕ}
    (hq : 0 < q)
    (hSlope : residualSlope β = (p : ℝ) / (q : ℝ))
    (hn : 0 < n)
    (hNotDvd : ¬ q ∣ n * p) :
    q * roofResidual β n < n * p ∧
      n * p < q * (roofResidual β n + 1) := by
  have Sscaled :=
    U.residualSlope_scaledRational_of_eq_div hq hSlope
  exact rationalSlope_strictWindow_of_not_dvd Sscaled hn hNotDvd

end HasUnitCarry
end Experimental
end Collatz3
