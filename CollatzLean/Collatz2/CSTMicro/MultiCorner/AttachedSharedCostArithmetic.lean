import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadCellCostObstruction

/-!
# MultiCorner attached branch: 共有 cell-cost 予算の純算術

attached の最後の二つの exposed predecessor を同時に見るための、
Ferrers 幾何から独立した整数算術 checkpoint。

一つの minimal bad word に対して

* `M = 2^H` : 共通 modulus
* `G = M - 3^m` : terminal gap
* `q` : normalized separation defect
* `R` : least representative
* `C₀, C₁ = G - D₀, G - D₁` : 二つの predecessor cell cost
* `δ₀, δ₁` : representative increment
* `w₀, w₁` : affine cell weight

を考える。

各 cell の exact identity

  M C_j = G δ_j + w_j

と bad word の affine decomposition

  B = G R + M q

から、二つの cell が共有する予算 `G-q` と representative threshold `M+R` の間に
exact identity を得る。

重要なのは、これは attached を排除したという主張ではないこと。
ここでは「二つの corner を同時に使うと、一個の共有予算 `G-q` が現れる」ことだけを
数学的に固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

/--
attached の二つの predecessor cell に共通する純算術データ。

`extra_pos` は後段の strict comparison に必要な

  0 < B + w₀ + w₁

をまとめたもの。actual CST 適用では affine numerator と二つの cell weight が
正であることから与える。
-/
structure AttachedSharedCostPair where
  modulus : ℤ
  gap : ℤ
  affineB : ℤ
  normalizedQ : ℤ
  representative : ℤ
  cost0 : ℤ
  cost1 : ℤ
  delta0 : ℤ
  delta1 : ℤ
  weight0 : ℤ
  weight1 : ℤ

  modulus_pos : 0 < modulus
  gap_pos : 0 < gap

  affine_decomposition :
    affineB = gap * representative + modulus * normalizedQ

  cell0_exact :
    modulus * cost0 = gap * delta0 + weight0
  cell1_exact :
    modulus * cost1 = gap * delta1 + weight1

  extra_pos : 0 < affineB + weight0 + weight1

namespace AttachedSharedCostPair

/-- 二つの cell cost の和。 -/
def costSum (P : AttachedSharedCostPair) : ℤ :=
  P.cost0 + P.cost1

/-- 二つの representative increment の和。 -/
def deltaSum (P : AttachedSharedCostPair) : ℤ :=
  P.delta0 + P.delta1

/-- minimal bad の二つの corner が共有する cost budget。 -/
def sharedBudget (P : AttachedSharedCostPair) : ℤ :=
  P.gap - P.normalizedQ

/-- double predecessor の carry/no-carry を分ける representative threshold。 -/
def representativeThreshold (P : AttachedSharedCostPair) : ℤ :=
  P.modulus + P.representative

/--
二つの cell identity と bad affine decomposition を一つにまとめた master identity。

  M (C₀+C₁-(G-q))
    = G (δ₀+δ₁-(M+R)) + (B+w₀+w₁).

左辺は共有 cost budget からの超過量、右辺第一項は double predecessor の
representative carry threshold からの超過量である。
-/
theorem sharedCost_master_identity
    (P : AttachedSharedCostPair) :
    P.modulus * (P.costSum - P.sharedBudget) =
      P.gap * (P.deltaSum - P.representativeThreshold) +
        (P.affineB + P.weight0 + P.weight1) := by
  unfold costSum sharedBudget deltaSum representativeThreshold
  calc
    P.modulus *
        ((P.cost0 + P.cost1) - (P.gap - P.normalizedQ)) =
      P.modulus * P.cost0 + P.modulus * P.cost1 -
        P.modulus * P.gap + P.modulus * P.normalizedQ := by
          ring
    _ =
      (P.gap * P.delta0 + P.weight0) +
        (P.gap * P.delta1 + P.weight1) -
        P.modulus * P.gap + P.modulus * P.normalizedQ := by
          rw [P.cell0_exact, P.cell1_exact]
    _ =
      P.gap *
          ((P.delta0 + P.delta1) -
            (P.modulus + P.representative)) +
        (P.affineB + P.weight0 + P.weight1) := by
          rw [P.affine_decomposition]
          ring

/--
下側の second edge が carry 側、すなわち

  M + R < δ₀ + δ₁

なら、二つの cell cost の和は共有予算を strict に超える。

  G-q < C₀+C₁.
-/
theorem sharedBudget_lt_costSum_of_representativeCarry
    (P : AttachedSharedCostPair)
    (hCarry : P.representativeThreshold < P.deltaSum) :
    P.sharedBudget < P.costSum := by
  have hMaster := P.sharedCost_master_identity
  have hDeltaPos : 0 < P.deltaSum - P.representativeThreshold := by
    exact sub_pos.mpr hCarry
  have hGapTerm :
      0 < P.gap * (P.deltaSum - P.representativeThreshold) :=
    mul_pos P.gap_pos hDeltaPos
  have hRight :
      0 <
        P.gap * (P.deltaSum - P.representativeThreshold) +
          (P.affineB + P.weight0 + P.weight1) :=
    add_pos hGapTerm P.extra_pos
  have hLeft : 0 < P.modulus * (P.costSum - P.sharedBudget) := by
    rw [hMaster]
    exact hRight
  nlinarith [P.modulus_pos]

/--
下側の second edge が no-carry 側にあり、double predecessor が safe なら、
二つの cost の和は共有予算より strict に小さい。

safe 条件は normalized defect で

  q - (G-C₀) - (G-C₁) + G < 0

と書いている。整理するとそのまま

  C₀+C₁ < G-q

になる。
-/
theorem costSum_lt_sharedBudget_of_doubleSafeNoCarry
    (P : AttachedSharedCostPair)
    (hSafe :
      P.normalizedQ - (P.gap - P.cost0) -
          (P.gap - P.cost1) + P.gap < 0) :
    P.costSum < P.sharedBudget := by
  unfold costSum sharedBudget
  linarith

/--
actual double predecessor の no-carry branch が safe である、という一個の仮定だけで、
attached の二角は共有予算 `G-q` の上下に完全分岐する。

* `δ₀+δ₁ ≤ M+R` なら `C₀+C₁ < G-q`
* `M+R < δ₀+δ₁` なら `G-q < C₀+C₁`

したがって equality は許されない。
-/
theorem sharedCost_branch_dichotomy
    (P : AttachedSharedCostPair)
    (hDoubleSafeNoCarry :
      P.deltaSum ≤ P.representativeThreshold →
        P.normalizedQ - (P.gap - P.cost0) -
            (P.gap - P.cost1) + P.gap < 0) :
    (P.deltaSum ≤ P.representativeThreshold ∧
        P.costSum < P.sharedBudget) ∨
      (P.representativeThreshold < P.deltaSum ∧
        P.sharedBudget < P.costSum) := by
  rcases le_or_gt P.deltaSum P.representativeThreshold with hNoCarry | hCarry
  · left
    exact ⟨hNoCarry,
      P.costSum_lt_sharedBudget_of_doubleSafeNoCarry
        (hDoubleSafeNoCarry hNoCarry)⟩
  · right
    exact ⟨hCarry,
      P.sharedBudget_lt_costSum_of_representativeCarry hCarry⟩

/-- 上の二分岐から共有予算との equality は排除される。 -/
theorem costSum_ne_sharedBudget
    (P : AttachedSharedCostPair)
    (hDoubleSafeNoCarry :
      P.deltaSum ≤ P.representativeThreshold →
        P.normalizedQ - (P.gap - P.cost0) -
            (P.gap - P.cost1) + P.gap < 0) :
    P.costSum ≠ P.sharedBudget := by
  intro hEq
  rcases P.sharedCost_branch_dichotomy hDoubleSafeNoCarry with hLow | hHigh
  · rw [hEq] at hLow
    exact (lt_irrefl P.sharedBudget) hLow.2
  · rw [hEq] at hHigh
    exact (lt_irrefl P.sharedBudget) hHigh.2

end AttachedSharedCostPair

end MultiCorner
end CSTMicro
end Collatz2
