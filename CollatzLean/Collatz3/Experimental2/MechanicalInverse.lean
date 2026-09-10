import CollatzLean.Collatz3.Experimental2.MechanicalRoofDerived
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Collatz3 Experimental2: lower mechanical roof の離散逆

`Experimental2` では lower mechanical roof を

`β(n) = floor(n * σ)`

という full slope `σ` で直接扱う。
このファイルでは、その屋根を高さ側から逆向きに読む。

`H(k) = min {m | k ≤ β(m)}`

を離散逆とすると、`1 ≤ σ` のもとで

`H(k) = ceil(k / σ)`

となる。したがって inverse height は slope `1 / σ` の upper / ceil mechanical height であり、
一歩差分は `0` または `1` になる。

Collatz specialization では `σ = log₂ 3` なので、逆 slope は `log₃ 2` になる。
この層には `2`, `3`, `beattyIndex`, `RecordFerrers` を持ち込まない。
-/

namespace Collatz3
namespace Experimental2

/-- 任意の高さがどこかの roof value 以下に入ること。 -/
def IsCofinalRoof (β : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, k ≤ β m

/--
cofinal roof の離散逆。

`k ≤ β(m)` を初めて満たす最小 `m` を返す。
proof argument は Prop なので、数学的 data を新しい structure に保存しない。
-/
def inverseHeight
    (β : ℕ → ℕ)
    (C : IsCofinalRoof β)
    (k : ℕ) : ℕ :=
  Nat.find (C k)

/-- 離散逆は定義した高さへ実際に到達する。 -/
theorem inverseHeight_spec
    {β : ℕ → ℕ}
    (C : IsCofinalRoof β)
    (k : ℕ) :
    k ≤ β (inverseHeight β C k) := by
  exact Nat.find_spec (C k)

/-- 離散逆より前では、まだ高さ `k` に届かない。 -/
theorem inverseHeight_min
    {β : ℕ → ℕ}
    (C : IsCofinalRoof β)
    {k m : ℕ}
    (hm : m < inverseHeight β C k) :
    β m < k := by
  by_contra hnot
  have hReach : k ≤ β m := by omega
  have hMin : inverseHeight β C k ≤ m :=
    Nat.find_min' (C k) hReach
  omega

/-- `m` ですでに高さ `k` に届くなら、離散逆は `m` 以下。 -/
theorem inverseHeight_le_of_reaches
    {β : ℕ → ℕ}
    (C : IsCofinalRoof β)
    {k m : ℕ}
    (hReach : k ≤ β m) :
    inverseHeight β C k ≤ m := by
  exact Nat.find_min' (C k) hReach

/-- threshold を上げると離散逆 index は下がらない。 -/
theorem inverseHeight_mono
    {β : ℕ → ℕ}
    (C : IsCofinalRoof β)
    {k l : ℕ}
    (hkl : k ≤ l) :
    inverseHeight β C k ≤ inverseHeight β C l := by
  apply inverseHeight_le_of_reaches C
  exact le_trans hkl (inverseHeight_spec C l)

/-- `ceil(k * λ)` 型の upper mechanical height。 -/
def IsUpperMechanicalHeight
    (H : ℕ → ℕ)
    («λ» : ℝ) : Prop :=
  ∀ k : ℕ, H k = ⌈(k : ℝ) * «λ»⌉₊

/-- upper mechanical height の一歩差分。 -/
noncomputable def upperMechanicalHeightBit
    («λ» : ℝ)
    (k : ℕ) : ℕ :=
  ⌈((k + 1 : ℕ) : ℝ) * «λ»⌉₊ -
    ⌈(k : ℝ) * «λ»⌉₊

namespace IsLowerMechanicalRoof

/--
full slope が `1` 以上なら lower mechanical roof は自動的に cofinal。

`β(k) ≤ kσ < β(k)+1` と `k ≤ kσ` から `k ≤ β(k)` が従う。
-/
theorem cofinal_of_one_le_slope
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ) :
    IsCofinalRoof β := by
  intro k
  refine ⟨k, ?_⟩
  have hCell := M k
  have hkσ : (k : ℝ) ≤ (k : ℝ) * σ := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith
  have hLt : (k : ℝ) < ((β k + 1 : ℕ) : ℝ) :=
    lt_of_le_of_lt hkσ (by simpa using hCell.2)
  have hNat : k < β k + 1 := by
    exact_mod_cast hLt
  omega

/-- `1 ≤ σ` の lower mechanical roof に対する canonical 離散逆。 -/
def inverse
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) : ℕ :=
  inverseHeight β (M.cofinal_of_one_le_slope hσ) k

/-- canonical 離散逆の到達条件。 -/
theorem inverse_spec
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    k ≤ β (M.inverse hσ k) := by
  exact inverseHeight_spec (M.cofinal_of_one_le_slope hσ) k

/-- canonical 離散逆の最小性。 -/
theorem inverse_min
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {k m : ℕ}
    (hm : m < M.inverse hσ k) :
    β m < k := by
  exact inverseHeight_min (M.cofinal_of_one_le_slope hσ) hm

/-- canonical 離散逆の upper-bound elimination。 -/
theorem inverse_le_of_reaches
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {k m : ℕ}
    (hReach : k ≤ β m) :
    M.inverse hσ k ≤ m := by
  exact inverseHeight_le_of_reaches (M.cofinal_of_one_le_slope hσ) hReach

/-- canonical 離散逆は threshold に対して単調。 -/
theorem inverse_mono
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    {k l : ℕ}
    (hkl : k ≤ l) :
    M.inverse hσ k ≤ M.inverse hσ l := by
  exact inverseHeight_mono (M.cofinal_of_one_le_slope hσ) hkl

/-- canonical 離散逆は `0` を `0` に送る。 -/
@[simp] theorem inverse_zero
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ) :
    M.inverse hσ 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply M.inverse_le_of_reaches hσ
  exact Nat.zero_le _

/--
離散逆の closed form。

`β(n) = floor(nσ)` かつ `1 ≤ σ` なら

`H(k) = ceil(k / σ)`。

これが full-slope roof と inverse height を結ぶ中心 theorem。
-/
theorem inverse_eq_natCeil_div
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverse hσ k = ⌈(k : ℝ) / σ⌉₊ := by
  by_cases hk : k = 0
  · subst k
    simp [M.inverse_zero hσ]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    let H := M.inverse hσ k
    have hHPos : 0 < H := by
      by_contra hnot
      have hHZero : H = 0 := Nat.eq_zero_of_not_pos hnot
      have hSpec := M.inverse_spec hσ k
      have hBetaZero := M.eq_natFloor' 0
      simp only [CharP.cast_eq_zero, zero_mul, Nat.floor_zero] at hBetaZero
      dsimp [H] at hHZero
      rw [hHZero, hBetaZero] at hSpec
      omega
    have hSigmaPos : (0 : ℝ) < σ := lt_of_lt_of_le (by norm_num) hσ
    have hSpec := M.inverse_spec hσ k
    have hCellH := M H
    have hRightMul :
        (k : ℝ) ≤ (H : ℝ) * σ := by
      have hSpecR : (k : ℝ) ≤ (β H : ℝ) := by
        exact_mod_cast hSpec
      exact le_trans hSpecR hCellH.1
    have hPredLt : H - 1 < H := by omega
    have hMinPred := M.inverse_min hσ (k := k) hPredLt
    have hCellPred := M (H - 1)
    have hPredSuccLe : β (H - 1) + 1 ≤ k := by omega
    have hPredSuccLeR :
        ((β (H - 1) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hPredSuccLe
    have hLeftMul :
        (((H - 1 : ℕ) : ℝ) * σ) < (k : ℝ) := by
      exact lt_of_lt_of_le hCellPred.2 (by simpa using hPredSuccLeR)
    have hLeft :
        (((H - 1 : ℕ) : ℝ)) < (k : ℝ) / σ := by
      exact (lt_div_iff₀ hSigmaPos).2 hLeftMul
    have hRight :
        (k : ℝ) / σ ≤ (H : ℝ) := by
      exact (div_le_iff₀ hSigmaPos).2 hRightMul
    have hCeil :
        ⌈(k : ℝ) / σ⌉₊ = H := by
      apply (Nat.ceil_eq_iff (Nat.ne_of_gt hHPos)).2
      exact ⟨hLeft, hRight⟩
    exact hCeil.symm

/-- inverse-height slope。 -/
noncomputable def inverseSlope (σ : ℝ) : ℝ :=
  σ⁻¹

/-- division 形を slope multiplication 形へ書き換えた closed form。 -/
theorem inverse_eq_natCeil_mul_inverseSlope
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverse hσ k =
      ⌈(k : ℝ) * inverseSlope σ⌉₊ := by
  rw [M.inverse_eq_natCeil_div hσ]
  simp [inverseSlope, div_eq_mul_inv]

/-- 離散逆は一歩で下がらない。 -/
theorem inverse_le_succ
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverse hσ k ≤ M.inverse hσ (k + 1) := by
  exact M.inverse_mono hσ (by omega)

/--
離散逆は一歩で高々 `1` しか増えない。

`1 ≤ σ` と lower mechanical cell だけから、
index を一つ進めれば roof height は少なくとも一つ増える。
-/
theorem inverse_succ_le_add_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverse hσ (k + 1) ≤ M.inverse hσ k + 1 := by
  let H := M.inverse hσ k
  have hSpec : k ≤ β H := by
    simpa [H] using M.inverse_spec hσ k
  have hCellH := M H
  have hCellNext := M (H + 1)
  have hSigmaStep :
      (H : ℝ) * σ + 1 ≤ ((H + 1 : ℕ) : ℝ) * σ := by
    push_cast
    nlinarith
  have hRiseR :
      (β H : ℝ) + 1 < (β (H + 1) : ℝ) + 1 := by
    have h1 : (β H : ℝ) + 1 ≤ (H : ℝ) * σ + 1 := by
      linarith [hCellH.1]
    have h2 :
        ((H + 1 : ℕ) : ℝ) * σ < (β (H + 1) : ℝ) + 1 :=
      hCellNext.2
    exact lt_of_le_of_lt (le_trans h1 hSigmaStep) h2
  have hRise : β H + 1 ≤ β (H + 1) := by
    have hRiseNat : β H + 1 < β (H + 1) + 1 := by
      exact_mod_cast hRiseR
    omega
  have hReach : k + 1 ≤ β (H + 1) := by
    omega
  exact M.inverse_le_of_reaches hσ hReach

/-- inverse height の一歩差分。 -/
def inverseStep
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) : ℕ :=
  M.inverse hσ (k + 1) - M.inverse hσ k

/-- inverse-height increment は exact に `0` または `1`。 -/
theorem inverseStep_eq_zero_or_one
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverseStep hσ k = 0 ∨ M.inverseStep hσ k = 1 := by
  have hLower := M.inverse_le_succ hσ k
  have hUpper := M.inverse_succ_le_add_one hσ k
  unfold inverseStep
  omega

/--
離散逆の increment は slope `1/σ` の upper/ceil mechanical bit そのもの。
-/
theorem inverseStep_eq_upperMechanicalHeightBit
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ)
    (k : ℕ) :
    M.inverseStep hσ k =
      upperMechanicalHeightBit (inverseSlope σ) k := by
  unfold inverseStep upperMechanicalHeightBit
  rw [M.inverse_eq_natCeil_mul_inverseSlope hσ (k + 1)]
  rw [M.inverse_eq_natCeil_mul_inverseSlope hσ k]

/-- canonical 離散逆全体が upper mechanical height になる。 -/
theorem inverse_isUpperMechanicalHeight
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (hσ : (1 : ℝ) ≤ σ) :
    IsUpperMechanicalHeight (M.inverse hσ) (inverseSlope σ) := by
  intro k
  exact M.inverse_eq_natCeil_mul_inverseSlope hσ k

end IsLowerMechanicalRoof

end Experimental2
end Collatz3
