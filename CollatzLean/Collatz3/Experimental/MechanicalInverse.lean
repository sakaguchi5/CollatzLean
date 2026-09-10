import CollatzLean.Collatz3.Experimental.UnitCarryMechanicalCharacterization
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Collatz3 experimental: lower mechanical roof の離散逆

このファイルでは lower mechanical roof

`β(n) = n + floor(nρ)`

を「高さ `k` に初めて到達する index」から逆向きに読む。

重要なのは、Collatz 固有の `2^k < 3^m` を primitive に置かないことである。
一般の lower mechanical roof に対して

`H(k) = min {m | k ≤ β(m)}`

を定義し、`H` が slope `1 / (1 + ρ)` の upper/ceil mechanical height になることを示す。

この層に `2`, `3`, `beattyIndex`, `RecordFerrers` は現れない。
-/

namespace Collatz3
namespace Experimental

/-- 任意の高さがどこかの roof value 以下に入ること。 -/
def IsCofinalRoof (β : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, k ≤ β m

/--
cofinal roof `β` の離散逆。

`k ≤ β(m)` を初めて満たす最小 `m` を返す。
証明引数は proposition なので、数学的 data を増やすための structure にはしない。
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

/-- 離散逆より前ではまだ高さ `k` に届かない。 -/
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

/-- `ceil(nλ)` 型の mechanical height であることを表す薄い predicate。 -/
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
linear part が `1` の lower mechanical roof は自動的に cofinal。
実際 `β(k) = k + floor(kρ) ≥ k`。
-/
theorem cofinal_of_linear_one
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ) :
    IsCofinalRoof β := by
  intro k
  refine ⟨k, ?_⟩
  rw [M.eq_linear_add_natFloor]
  simp

/-- linear part `1` の lower mechanical roof に対する canonical 離散逆。 -/
def inverse
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) : ℕ :=
  inverseHeight β M.cofinal_of_linear_one k

/-- canonical 離散逆の到達条件。 -/
theorem inverse_spec
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    k ≤ β (M.inverse k) := by
  exact inverseHeight_spec M.cofinal_of_linear_one k

/-- canonical 離散逆の最小性。 -/
theorem inverse_min
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    {k m : ℕ}
    (hm : m < M.inverse k) :
    β m < k := by
  exact inverseHeight_min M.cofinal_of_linear_one hm

/-- canonical 離散逆の upper-bound elimination。 -/
theorem inverse_le_of_reaches
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    {k m : ℕ}
    (hReach : k ≤ β m) :
    M.inverse k ≤ m := by
  exact inverseHeight_le_of_reaches M.cofinal_of_linear_one hReach

/-- canonical 離散逆は threshold に対して単調。 -/
theorem inverse_mono
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    {k l : ℕ}
    (hkl : k ≤ l) :
    M.inverse k ≤ M.inverse l := by
  exact inverseHeight_mono M.cofinal_of_linear_one hkl

/--
`β(n) = n + floor(nρ)` は、shifted slope `1+ρ` に対する通常の floor cell と同じ。

この theorem が roof と inverse height をつなぐ中心 bridge である。
-/
theorem shiftedSlope_isNatFloor
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (n : ℕ) :
    IsNatFloor (β n) ((n : ℝ) * (1 + ρ)) := by
  obtain ⟨r, hBeta, hCell⟩ := M.2 n
  have hCell' :
      (r : ℝ) ≤ (n : ℝ) * ρ ∧
        (n : ℝ) * ρ < (r : ℝ) + 1 := by
    simpa [IsNatFloor] using hCell
  constructor
  · rw [hBeta]
    push_cast
    nlinarith
  · rw [hBeta]
    push_cast
    nlinarith

/-- canonical 離散逆は `0` を `0` に送る。 -/
@[simp] theorem inverse_zero
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ) :
    M.inverse 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply M.inverse_le_of_reaches
  exact Nat.zero_le _

/--
離散逆の closed form。

`β(n) = n + floor(nρ)` なら

`H(k) = ceil(k / (1 + ρ))`。

したがって roof slope `1+ρ` と inverse-height slope `1/(1+ρ)` は完全に双対である。
-/
theorem inverse_eq_natCeil_div_one_add
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverse k = ⌈(k : ℝ) / (1 + ρ)⌉₊ := by
  by_cases hk : k = 0
  · subst k
    simp [M.inverse_zero]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    let H := M.inverse k
    have hHPos : 0 < H := by
      by_contra hnot
      have hHZero : H = 0 := Nat.eq_zero_of_not_pos hnot
      have hSpec := M.inverse_spec k
      have hBetaZero := M.eq_linear_add_natFloor 0
      simp only [mul_one, CharP.cast_eq_zero, zero_mul, Nat.floor_zero, add_zero] at hBetaZero
      dsimp [H] at hHZero
      rw [hHZero, hBetaZero] at hSpec
      omega
    have hSigmaPos : (0 : ℝ) < 1 + ρ := by
      linarith [M.1]
    have hSpec := M.inverse_spec k
    have hCellH := M.shiftedSlope_isNatFloor H
    have hRightMul :
        (k : ℝ) ≤ (H : ℝ) * (1 + ρ) := by
      have hSpecR : (k : ℝ) ≤ (β H : ℝ) := by
        exact_mod_cast hSpec
      exact le_trans hSpecR hCellH.1
    have hPredLt : H - 1 < H := by omega
    have hMinPred := M.inverse_min (k := k) hPredLt
    have hCellPred := M.shiftedSlope_isNatFloor (H - 1)
    have hPredSuccLe : β (H - 1) + 1 ≤ k := by omega
    have hPredSuccLeR :
        ((β (H - 1) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hPredSuccLe
    have hCellPredUpper :
        (((H - 1 : ℕ) : ℝ) * (1 + ρ)) <
          ((β (H - 1) + 1 : ℕ) : ℝ) := by
      norm_num [IsNatFloor] at hCellPred ⊢
      exact hCellPred.2
    have hLeftMul :
        (((H - 1 : ℕ) : ℝ) * (1 + ρ)) < (k : ℝ) := by
      exact lt_of_lt_of_le hCellPredUpper hPredSuccLeR
    have hLeft :
        (((H - 1 : ℕ) : ℝ)) < (k : ℝ) / (1 + ρ) := by
      exact (lt_div_iff₀ hSigmaPos).2 hLeftMul
    have hRight :
        (k : ℝ) / (1 + ρ) ≤ (H : ℝ) := by
      exact (div_le_iff₀ hSigmaPos).2 hRightMul
    have hCeil :
        ⌈(k : ℝ) / (1 + ρ)⌉₊ = H := by
      apply (Nat.ceil_eq_iff (Nat.ne_of_gt hHPos)).2
      exact ⟨hLeft, hRight⟩
    exact hCeil.symm

/-- inverse-height slope。 -/
noncomputable def inverseSlope (ρ : ℝ) : ℝ :=
  (1 + ρ)⁻¹

/-- division 形を slope multiplication 形へ書き換えた closed form。 -/
theorem inverse_eq_natCeil_mul_inverseSlope
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverse k =
      ⌈(k : ℝ) * inverseSlope ρ⌉₊ := by
  rw [M.inverse_eq_natCeil_div_one_add]
  simp [inverseSlope, div_eq_mul_inv]

/-- 離散逆は一歩で下がらない。 -/
theorem inverse_le_succ
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverse k ≤ M.inverse (k + 1) := by
  exact M.inverse_mono (by omega)

/--
離散逆は一歩で高々 `1` しか増えない。

roof の linear part が `1` なので、roof index を一つ進めれば高さは少なくとも一つ増える。
-/
theorem inverse_succ_le_add_one
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverse (k + 1) ≤ M.inverse k + 1 := by
  let H := M.inverse k
  have hSpec : k ≤ β H := by
    simpa [H] using M.inverse_spec k
  have U : HasUnitCarry β := M.hasUnitCarry
  have hBetaOne : 1 ≤ β 1 := by
    rw [M.eq_linear_add_natFloor 1]
    simp
  have hAdd := U.add_eq H 1
  have hReach : k + 1 ≤ β (H + 1) := by
    rw [hAdd]
    omega
  exact M.inverse_le_of_reaches hReach

/-- inverse height の一歩差分。 -/
def inverseStep
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) : ℕ :=
  M.inverse (k + 1) - M.inverse k

/-- inverse-height increment は exact に `0` または `1`。 -/
theorem inverseStep_eq_zero_or_one
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverseStep k = 0 ∨ M.inverseStep k = 1 := by
  have hLower := M.inverse_le_succ k
  have hUpper := M.inverse_succ_le_add_one k
  unfold inverseStep
  omega

/--
離散逆の increment は slope `1/(1+ρ)` の upper/ceil mechanical bit そのもの。
-/
theorem inverseStep_eq_upperMechanicalHeightBit
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ)
    (k : ℕ) :
    M.inverseStep k =
      upperMechanicalHeightBit (inverseSlope ρ) k := by
  unfold inverseStep upperMechanicalHeightBit
  rw [M.inverse_eq_natCeil_mul_inverseSlope (k + 1)]
  rw [M.inverse_eq_natCeil_mul_inverseSlope k]

/-- canonical 離散逆全体が upper mechanical height になる。 -/
theorem inverse_isUpperMechanicalHeight
    {β : ℕ → ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β 1 ρ) :
    IsUpperMechanicalHeight M.inverse (inverseSlope ρ) := by
  intro k
  exact M.inverse_eq_natCeil_mul_inverseSlope k

end IsLowerMechanicalRoof

end Experimental
end Collatz3
