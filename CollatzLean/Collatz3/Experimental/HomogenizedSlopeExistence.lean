import CollatzLean.Collatz3.Experimental.UnitCarryClassification
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Collatz3 experimental: unit-carry roof から homogenized slope を構成する

これまで `IsHomogenizedSlope β ρ` は分類層への薄い入力として仮定していた。
このファイルでは、その仮定自体を `HasUnitCarry β` から派生させる。

Fekete の極限定理を black box として直接保存する代わりに、residual

`γ(n) = roofResidual β n`

が持つ

* 超加法性 `γ(a)+γ(b) ≤ γ(a+b)`
* 一単位上側誤差 `γ(a+b) ≤ γ(a)+γ(b)+1`

を共通倍数で衝突させる。

正整数 `m,n` に対して

`γ(m)/m < (γ(n)+1)/n`

が得られるので、全 lower ratio の上限を `ρ` と取れば exact に

`γ(n) ≤ nρ ≤ γ(n)+1`

となる。

したがって slope は primitive data ではなく、unit-carry roof から構成される derived object になる。
-/

namespace Collatz3
namespace Experimental

/-- 正の幅 `n` における residual の平均。`n=0` は集合側で除外する。 -/
noncomputable def residualRatio
    (β : ℕ → ℕ)
    (n : ℕ) : ℝ :=
  (roofResidual β n : ℝ) / (n : ℝ)

/-- slope window の上端に対応する平均。 -/
noncomputable def residualUpperRatio
    (β : ℕ → ℕ)
    (n : ℕ) : ℝ :=
  ((roofResidual β n : ℝ) + 1) / (n : ℝ)

/-- 全正整数幅から得られる lower residual ratio の集合。 -/
def residualRatioSet
    (β : ℕ → ℕ) : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = residualRatio β n}

/--
unit-carry roof から構成する canonical homogenized slope。

正幅 residual ratio 全体の上限を取る。
-/
noncomputable def residualSlope
    (β : ℕ → ℕ) : ℝ :=
  sSup (residualRatioSet β)

namespace HasUnitCarry

/--
residual を同じ幅 `r` で `k` 回連結したときの下側評価。

`k * γ(r) ≤ γ(k*r)`。
-/
theorem residual_mul_lower
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ k r : ℕ,
      k * roofResidual β r ≤ roofResidual β (k * r)
  | 0, r => by
      simp [U.roofResidual_zero]
  | Nat.succ k, r => by
      have hPrev := U.residual_mul_lower k r
      have hAdd := U.residual_add_eq (k * r) r
      calc
        (k + 1) * roofResidual β r =
            k * roofResidual β r + roofResidual β r := by
              simp [Nat.add_mul]
        _ ≤ roofResidual β (k * r) + roofResidual β r :=
          Nat.add_le_add_right hPrev (roofResidual β r)
        _ ≤ roofResidual β (k * r) + roofResidual β r +
              roofCarry β (k * r) r := by
          omega
        _ = roofResidual β ((k + 1) * r) := by
          rw [← hAdd]
          congr 1
          simp [Nat.add_mul]

/--
residual を同じ幅 `r` で `k+1` 回連結したときの sharp な上側評価。

各接合 carry が高々 `1` なので
`γ((k+1)r) ≤ (k+1)γ(r)+k`。
-/
theorem residual_mul_upper_succ
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ k r : ℕ,
      roofResidual β ((k + 1) * r) ≤
        (k + 1) * roofResidual β r + k
  | 0, r => by
      simp
  | Nat.succ k, r => by
      have hPrev := U.residual_mul_upper_succ k r
      have hAdd := U.residual_add_eq ((k + 1) * r) r
      have hCarryLe := U.carry_le_one ((k + 1) * r) r
      calc
        roofResidual β (((k + 1) + 1) * r) =
            roofResidual β ((k + 1) * r + r) := by
              congr 1
              simp [Nat.add_mul]
        _ = roofResidual β ((k + 1) * r) + roofResidual β r +
              roofCarry β ((k + 1) * r) r := hAdd
        _ ≤ ((k + 1) * roofResidual β r + k) +
              roofResidual β r + 1 := by
          omega
        _ = ((k + 1) + 1) * roofResidual β r + (k + 1) := by
          simp only [Nat.add_mul]
          omega

/--
共通倍数 `mn` で residual の下側反復と上側反復を比較する。

正整数 `m,n` について
`n*γ(m) < m*(γ(n)+1)`。

これが slope existence の中心となる有限算術補題。
-/
theorem residual_cross_mul_lt
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m n : ℕ}
    (hm : 0 < m) :
    n * roofResidual β m <
      m * (roofResidual β n + 1) := by
  cases m with
  | zero => omega
  | succ k =>
      have hLower := U.residual_mul_lower n (k + 1)
      have hUpper := U.residual_mul_upper_succ k n
      have hComm : n * (k + 1) = (k + 1) * n := Nat.mul_comm _ _
      rw [hComm] at hLower
      calc
        n * roofResidual β (k + 1) ≤
            roofResidual β ((k + 1) * n) := hLower
        _ ≤ (k + 1) * roofResidual β n + k := hUpper
        _ < (k + 1) * roofResidual β n + (k + 1) := by
          omega
        _ = (k + 1) * (roofResidual β n + 1) := by
          rw [Nat.mul_add]
          simp

/--
任意の lower ratio は任意の positive-width upper ratio より strict に小さい。

`γ(m)/m < (γ(n)+1)/n`。
-/
theorem residualRatio_lt_upperRatio
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m n : ℕ}
    (hm : 0 < m)
    (hn : 0 < n) :
    residualRatio β m < residualUpperRatio β n := by
  have hNat := U.residual_cross_mul_lt (m := m) (n := n) hm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hCast :
      (n : ℝ) * (roofResidual β m : ℝ) <
        (m : ℝ) * ((roofResidual β n : ℝ) + 1) := by
    exact_mod_cast hNat
  unfold residualRatio residualUpperRatio
  apply (div_lt_div_iff₀ hmR hnR).2
  nlinarith

/-- lower ratio 集合は空ではない。幅 `1` が常に入る。 -/
theorem residualRatioSet_nonempty
    {β : ℕ → ℕ} :
    (residualRatioSet β).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨1, by omega, ?_⟩
  simp [residualRatio, roofResidual]

/--
unit-carry の下で lower ratio 集合は上に有界。
実際、幅 `1` の upper ratio `1` が全 lower ratio の上界になる。
-/
theorem residualRatioSet_bddAbove
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    BddAbove (residualRatioSet β) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with ⟨m, hm, rfl⟩
  have h := U.residualRatio_lt_upperRatio hm (n := 1) (by omega)
  have hLe : residualRatio β m ≤ residualUpperRatio β 1 := le_of_lt h
  simpa [residualUpperRatio, roofResidual] using hLe

/-- 各 positive lower ratio は canonical slope 以下。 -/
theorem residualRatio_le_residualSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {n : ℕ}
    (hn : 0 < n) :
    residualRatio β n ≤ residualSlope β := by
  unfold residualSlope
  apply le_csSup U.residualRatioSet_bddAbove
  exact ⟨n, hn, rfl⟩

/--
canonical slope は各 positive width の upper ratio 以下。

全 lower ratio がその upper ratio より小さいことから `csSup_le` で出る。
-/
theorem residualSlope_le_upperRatio
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {n : ℕ}
    (hn : 0 < n) :
    residualSlope β ≤ residualUpperRatio β n := by
  unfold residualSlope
  apply csSup_le residualRatioSet_nonempty
  intro x hx
  rcases hx with ⟨m, hm, rfl⟩
  exact le_of_lt (U.residualRatio_lt_upperRatio hm hn)

/--
核心 bridge: canonical residual slope は exact homogenized slope window を満たす。

`γ(n) ≤ nρ ≤ γ(n)+1`。
-/
theorem residualSlope_isHomogenizedSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    IsHomogenizedSlope β (residualSlope β) := by
  intro n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hLowerRatio := U.residualRatio_le_residualSlope hn
  have hUpperRatio := U.residualSlope_le_upperRatio hn
  constructor
  · unfold residualRatio at hLowerRatio
    have h := (div_le_iff₀ hnR).mp hLowerRatio
    nlinarith
  · unfold residualUpperRatio at hUpperRatio
    have h := (le_div_iff₀ hnR).mp hUpperRatio
    nlinarith

/--
これまで仮定していた homogenized slope の存在は、`HasUnitCarry` から派生する。

したがって全面書き換えでは slope existence を primitive field として保存する必要はない。
-/
theorem exists_homogenizedSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∃ ρ : ℝ, IsHomogenizedSlope β ρ := by
  exact ⟨residualSlope β, U.residualSlope_isHomogenizedSlope⟩

/-- canonical slope も自動的に unit interval `[0,1]` に入る。 -/
theorem residualSlope_mem_unitInterval
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    0 ≤ residualSlope β ∧ residualSlope β ≤ 1 := by
  exact homogenizedSlope_mem_unitInterval U.residualSlope_isHomogenizedSlope

end HasUnitCarry
end Experimental
end Collatz3
