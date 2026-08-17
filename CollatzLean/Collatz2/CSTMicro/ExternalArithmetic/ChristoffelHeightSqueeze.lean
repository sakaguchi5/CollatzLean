import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.LopezStollPacket

/-!
# Critical residue arithmetic: Archimedean height squeeze

López--Stoll / Christoffel 側から

  |P|, |Q| <= H q 2^q

が得られたとき、`0 <= R <= B` なら

  |P + RQ| <= H q 2^q (B+1).

一方 `2^e ∣ P+RQ` で右辺が `2^e` 未満なら、
その整数は 0 しかあり得ない。

ここでは absolute-value API に依存せず、上下二本の整数不等式として
height bound を持つ。これにより proof は ordered-ring arithmetic だけで閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- López--Stoll numerator/denominator に対する共通 Archimedean height bound。 -/
def HasChristoffelHeightBound
    (H q : ℕ) (P Q : ℤ) : Prop :=
  let M : ℕ := H * q * 2 ^ q
  (-(M : ℤ) ≤ P ∧ P ≤ (M : ℤ)) ∧
  (-(M : ℤ) ≤ Q ∧ Q ≤ (M : ℤ))

/-- `P + RQ` の signed height estimate。 -/
theorem linear_height_bounds
    {P Q : ℤ}
    {R M : ℕ}
    (hPlo : -((M : ℕ) : ℤ) ≤ P)
    (hPhi : P ≤ (M : ℤ))
    (hQlo : -((M : ℕ) : ℤ) ≤ Q)
    (hQhi : Q ≤ (M : ℤ)) :
    -(((M * (R + 1) : ℕ) : ℤ)) ≤ P + (R : ℤ) * Q ∧
      P + (R : ℤ) * Q ≤ ((M * (R + 1) : ℕ) : ℤ) := by
  have hRnonneg : (0 : ℤ) ≤ (R : ℤ) := by positivity
  have hRQlo :
      (R : ℤ) * (-((M : ℕ) : ℤ)) ≤ (R : ℤ) * Q :=
    mul_le_mul_of_nonneg_left hQlo hRnonneg
  have hRQhi :
      (R : ℤ) * Q ≤ (R : ℤ) * (M : ℤ) :=
    mul_le_mul_of_nonneg_left hQhi hRnonneg
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/--
positive modulus `2^e` で割り切れる整数が `(-2^e,2^e)` に入れば 0。
-/
theorem eq_zero_of_twoPow_dvd_of_between
    {e : ℕ}
    {z : ℤ}
    (hDiv : ((2 : ℤ) ^ e) ∣ z)
    (hLo : -((2 : ℤ) ^ e) < z)
    (hHi : z < (2 : ℤ) ^ e) :
    z = 0 := by
  rcases hDiv with ⟨c, hc⟩
  rw [hc] at hLo hHi ⊢
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hPowNonneg : (0 : ℤ) ≤ (2 : ℤ) ^ e := by positivity
    have hcCases : c ≤ -1 ∨ 1 ≤ c := by omega
    rcases hcCases with hcNeg | hcPos
    · have hMul :
          (2 : ℤ) ^ e * c ≤ (2 : ℤ) ^ e * (-1) :=
        mul_le_mul_of_nonneg_left hcNeg hPowNonneg
      have : (2 : ℤ) ^ e * c ≤ -((2 : ℤ) ^ e) := by
        simpa using hMul
      omega
    · have hMul :
          (2 : ℤ) ^ e * 1 ≤ (2 : ℤ) ^ e * c :=
        mul_le_mul_of_nonneg_left hcPos hPowNonneg
      have : (2 : ℤ) ^ e ≤ (2 : ℤ) ^ e * c := by
        simpa using hMul
      omega

/-- height bound と `R ≤ B` から linear form の signed height を抑える。 -/
theorem linear_height_bounds_of_le
    {H q B R : ℕ}
    {P Q : ℤ}
    (hHeight : HasChristoffelHeightBound H q P Q)
    (hR : R ≤ B) :
    -((((H * q * 2 ^ q) * (B + 1) : ℕ) : ℤ)) ≤
        P + (R : ℤ) * Q ∧
      P + (R : ℤ) * Q ≤
        (((H * q * 2 ^ q) * (B + 1) : ℕ) : ℤ) := by
  let M : ℕ := H * q * 2 ^ q
  change
    ((-(M : ℤ) ≤ P ∧ P ≤ (M : ℤ)) ∧
      (-(M : ℤ) ≤ Q ∧ Q ≤ (M : ℤ))) at hHeight
  rcases hHeight with
    ⟨⟨hPLower, hPUpper⟩, ⟨hQLower, hQUpper⟩⟩
  have hBase :=
    linear_height_bounds
      (P := P) (Q := Q) (R := R) (M := M)
      hPLower hPUpper hQLower hQUpper
  have hRB :
      M * (R + 1) ≤ M * (B + 1) := by
    apply Nat.mul_le_mul_left
    omega
  have hRBz :
      ((M * (R + 1) : ℕ) : ℤ) ≤
        ((M * (B + 1) : ℕ) : ℤ) := by
    exact_mod_cast hRB
  change
    -(((M * (B + 1) : ℕ) : ℤ)) ≤
        P + (R : ℤ) * Q ∧
      P + (R : ℤ) * Q ≤
        (((M * (B + 1) : ℕ) : ℤ))
  constructor
  · exact le_trans (by omega) hBase.1
  · exact le_trans hBase.2 hRBz

/--
small residue squeeze。

* packet と `R` が mod `2^e` で一致、
* `R <= B`,
* Christoffel height が `H q 2^q`,
* その全 height が `2^e` 未満、

なら exact equality `P+RQ=0` を強制する。
-/
theorem exactEquality_of_height_squeeze
    (A : LopezStollPacket)
    {e H B R : ℕ}
    (hMatch : A.Matches e R)
    (hHeight : HasChristoffelHeightBound H A.q A.P A.Q)
    (hR : R ≤ B)
    (hSqueeze :
      (H * A.q * 2 ^ A.q) * (B + 1) < 2 ^ e) :
    A.P + (R : ℤ) * A.Q = 0 := by
  have hBounds := linear_height_bounds_of_le hHeight hR
  have hCast :
      ((((H * A.q * 2 ^ A.q) * (B + 1) : ℕ) : ℤ)) <
        ((2 ^ e : ℕ) : ℤ) := by
    exact_mod_cast hSqueeze
  apply eq_zero_of_twoPow_dvd_of_between hMatch
  · have hNeg :
        -(((2 ^ e : ℕ) : ℤ)) <
          -((((H * A.q * 2 ^ A.q) * (B + 1) : ℕ) : ℤ)) := by
      exact neg_lt_neg hCast
    have hLo :
        -(((2 ^ e : ℕ) : ℤ)) <
          A.P + (R : ℤ) * A.Q := by
      exact lt_of_lt_of_le hNeg hBounds.1
    simpa using hLo
  · have hHi :
        A.P + (R : ℤ) * A.Q <
          (((2 ^ e : ℕ) : ℤ)) := by
      exact lt_of_le_of_lt hBounds.2 hCast
    simpa using hHi


/--
したがって packet が nonnegative exact equality を排除していれば、
上の条件を満たす small residue は存在しない。
-/
theorem noSmallResidue_of_height_squeeze
    (A : LopezStollPacket)
    {e H B R : ℕ}
    (hMatch : A.Matches e R)
    (hHeight : HasChristoffelHeightBound H A.q A.P A.Q)
    (hR : R ≤ B)
    (hSqueeze :
      (H * A.q * 2 ^ A.q) * (B + 1) < 2 ^ e) :
    False := by
  have hEq :=
    exactEquality_of_height_squeeze A hMatch hHeight hR hSqueeze
  exact A.exact_ne_zero R hEq

end ExternalArithmetic
end CSTMicro
end Collatz2
