import CollatzLean.Collatz4.Core.Forward

/-!
# Collatz4.General.ResidualBounds

残余語の `G` を長さ `r` と残り2指数 `E` から挟む一般理論。

正確な上下包絡線

* `G_min(E,r) = 3^(r+1) - 3*2^(r+1) + 2^(E+1)`
* `G_max(E,r) = 2^(E-r+2) * (3^r - 2^r) - 3^r`

を定義し、長さ境界を取るときには単調性の扱いやすい粗い包絡線

* `L(r)   = 3^(r+1) - 3*2^(r+1)`
* `U(E,r) = 2^(E-r+2) * 3^r`

へ落とす。

この層には m 固有の数値を置かない。
-/

namespace Collatz4.General

/-- 残余語に対する正確な下側包絡線。 -/
def residualGMin (E r : ℕ) : ℕ :=
  3 ^ (r + 1) - 3 * 2 ^ (r + 1) + 2 ^ (E + 1)

/-- 残余語に対する正確な上側包絡線。 -/
def residualGMax (E r : ℕ) : ℕ :=
  2 ^ (E - r + 2) * (3 ^ r - 2 ^ r) - 3 ^ r

/-- `G_min` から `E` 依存の正項を落とした粗い下界。 -/
def coarseResidualLower (r : ℕ) : ℕ :=
  3 ^ (r + 1) - 3 * 2 ^ (r + 1)

/-- `G_max` から負項と `-2^r` を落とした粗い上界。 -/
def coarseResidualUpper (E r : ℕ) : ℕ :=
  2 ^ (E - r + 2) * 3 ^ r

/--
残余量 `G` が正確な二つの包絡線の間にあることを表す。

実際の Collatz 残余語からこの構造を作ることが、意味論側の bridge になる。
-/
structure ResidualGBounds (G E r : ℕ) : Prop where
  lower : residualGMin E r ≤ G
  upper : G ≤ residualGMax E r

/-- 粗い下界は正確な `G_min` 以下。 -/
theorem coarseResidualLower_le_gMin (E r : ℕ) :
    coarseResidualLower r ≤ residualGMin E r := by
  simp [coarseResidualLower, residualGMin]

/-- 正確な `G_max` は粗い上界以下。 -/
theorem residualGMax_le_coarseResidualUpper (E r : ℕ) :
    residualGMax E r ≤ coarseResidualUpper E r := by
  unfold residualGMax coarseResidualUpper
  calc
    2 ^ (E - r + 2) * (3 ^ r - 2 ^ r) - 3 ^ r
        ≤ 2 ^ (E - r + 2) * (3 ^ r - 2 ^ r) := Nat.sub_le _ _
    _ ≤ 2 ^ (E - r + 2) * 3 ^ r :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)

namespace ResidualGBounds

/-- 正確な下側包絡線から粗い下界を取り出す。 -/
theorem coarseLower
    {G E r : ℕ} (h : ResidualGBounds G E r) :
    coarseResidualLower r ≤ G := by
  exact (coarseResidualLower_le_gMin E r).trans h.lower

/-- 正確な上側包絡線から粗い上界を取り出す。 -/
theorem coarseUpper
    {G E r : ℕ} (h : ResidualGBounds G E r) :
    G ≤ coarseResidualUpper E r := by
  exact h.upper.trans (residualGMax_le_coarseResidualUpper E r)

end ResidualGBounds

/-- 粗い下界は長さを1増やしても減らない。 -/
theorem coarseResidualLower_le_succ (r : ℕ) :
    coarseResidualLower r ≤ coarseResidualLower (r + 1) := by
  unfold coarseResidualLower
  have h3 : 3 ^ ((r + 1) + 1) = 3 * 3 ^ (r + 1) := by
    rw [pow_succ]
    ac_rfl
  have h2 : 3 * 2 ^ ((r + 1) + 1) = 2 * (3 * 2 ^ (r + 1)) := by
    rw [pow_succ]
    ring
  rw [h3, h2]
  omega

/-- 粗い下界は `r` に関して単調増加。 -/
theorem coarseResidualLower_monotone : Monotone coarseResidualLower := by
  exact monotone_nat_of_le_succ coarseResidualLower_le_succ

/-- 粗い上界は残り2指数 `E` に関して単調増加。 -/
theorem coarseResidualUpper_monotone_E (r : ℕ) :
    Monotone (fun E => coarseResidualUpper E r) := by
  intro E₁ E₂ hE
  unfold coarseResidualUpper
  have hexp : E₁ - r + 2 ≤ E₂ - r + 2 := by
    omega
  have hp : 2 ^ (E₁ - r + 2) ≤ 2 ^ (E₂ - r + 2) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp
  exact Nat.mul_le_mul_right (3 ^ r) hp

/-- 粗い上界は長さを1増やしても減らない。 -/
theorem coarseResidualUpper_le_succ (E r : ℕ) :
    coarseResidualUpper E r ≤ coarseResidualUpper E (r + 1) := by
  unfold coarseResidualUpper
  by_cases h : r < E
  · have hexp : E - r + 2 = (E - (r + 1) + 2) + 1 := by
      omega
    have h2 :
        2 ^ (E - r + 2) =
          2 * 2 ^ (E - (r + 1) + 2) := by
      rw [hexp, pow_succ]
      ac_rfl
    have h3 :
        3 ^ (r + 1) = 3 * 3 ^ r := by
      rw [pow_succ]
      ac_rfl
    rw [h2, h3]
    let A := 2 ^ (E - (r + 1) + 2)
    let B := 3 ^ r
    calc
      2 * A * B = 2 * (A * B) := by ac_rfl
      _ ≤ 3 * (A * B) := by
        exact Nat.mul_le_mul_right (A * B) (by omega)
      _ = A * (3 * B) := by ac_rfl
  · have hEr : E ≤ r := Nat.le_of_not_gt h
    have hsub1 : E - r = 0 := Nat.sub_eq_zero_of_le hEr
    have hsub2 : E - (r + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hsub1, hsub2]
    simp only [zero_add]
    have hp : 3 ^ r ≤ 3 ^ (r + 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) (Nat.le_succ r)
    exact Nat.mul_le_mul_left (2 ^ 2) hp

/-- 粗い上界は `r` に関して単調増加。 -/
theorem coarseResidualUpper_monotone_r (E : ℕ) :
    Monotone (coarseResidualUpper E) := by
  exact monotone_nat_of_le_succ (coarseResidualUpper_le_succ E)

/-- `E` と `r` を同時に大きくすると粗い上界は減らない。 -/
theorem coarseResidualUpper_mono
    {E₁ E₂ r₁ r₂ : ℕ}
    (hE : E₁ ≤ E₂)
    (hr : r₁ ≤ r₂) :
    coarseResidualUpper E₁ r₁ ≤ coarseResidualUpper E₂ r₂ := by
  calc
    coarseResidualUpper E₁ r₁
        ≤ coarseResidualUpper E₂ r₁ := coarseResidualUpper_monotone_E r₁ hE
    _ ≤ coarseResidualUpper E₂ r₂ := coarseResidualUpper_monotone_r E₂ hr

namespace ResidualGBounds

/--
粗い下界の境界一点が既に `G` を超えるなら、実際の長さはその境界より小さい。
-/
theorem length_lt_of_lower_boundary
    {G E r boundary : ℕ}
    (h : ResidualGBounds G E r)
    (hboundary : G < coarseResidualLower boundary) :
    r < boundary := by
  by_contra hnot
  have hbr : boundary ≤ r := Nat.le_of_not_gt hnot
  have hmono : coarseResidualLower boundary ≤ coarseResidualLower r :=
    coarseResidualLower_monotone hbr
  have hlo := h.coarseLower
  omega

/--
`E ≤ Emax` のもとで、境界長の粗い上界が既に `G` 未満なら、
実際の長さはその境界より大きい。
-/
theorem boundary_lt_length_of_upper_boundary
    {G E Emax r boundary : ℕ}
    (h : ResidualGBounds G E r)
    (hE : E ≤ Emax)
    (hboundary : coarseResidualUpper Emax boundary < G) :
    boundary < r := by
  by_contra hnot
  have hr : r ≤ boundary := Nat.le_of_not_gt hnot
  have hmono : coarseResidualUpper E r ≤ coarseResidualUpper Emax boundary :=
    coarseResidualUpper_mono hE hr
  have hup := h.coarseUpper
  omega

end ResidualGBounds

end Collatz4.General
