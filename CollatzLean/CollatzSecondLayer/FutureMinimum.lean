import CollatzLean.CollatzSecondLayer.InfiniteOrbit

/-!
# future-minimum

非有界軌道から抽出する候補点を、後続部分全体の最小値として記述する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 位置 `n` の値が、その後の軌道値以下であること。 -/
def FutureMinimumAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

/-- future-minimumから始まる任意の有限区間の終点は開始値以上である。 -/
theorem futureMinimum_le_segment_end
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n) (m : ℕ) :
    O.value n ≤ O.value (n + m) :=
  hmin (n + m) (by omega)

/-- 奇数軌道値は正である。 -/
lemma value_pos (O : OddOrbit) (n : ℕ) : 0 < O.value n := by
  rcases O.value_odd n with ⟨k, hk⟩
  omega

/-- 指数が `2` 以上であれば `2^k` は少なくとも `4` になる。 -/
lemma four_le_pow_of_two {k : ℕ} (hk : 2 ≤ k) :
    4 ≤ 2 ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add]
  have hp : 0 < 2 ^ m := Nat.pow_pos (by decide)
  omega

/--
`1` より大きいfuture-minimumでは、最初の2除算指数は必ず `1` である。
`1` の自明周期では指数 `2` が起こるため、値が `1` より大きいという条件を明記する。
-/
theorem exponent_eq_one_of_futureMinimum
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hgt : 1 < O.value n) :
    O.exponent n = 1 := by
  have he := O.exponent_pos n
  cases hE : O.exponent n with
  | zero => omega
  | succ e =>
      cases e with
      | zero => simp only [zero_add]
      | succ e =>
          have hpow : 4 ≤ 2 ^ O.exponent n := by
            apply four_le_pow_of_two
            rw [hE]
            omega
          have hnext : O.value n ≤ O.value (n + 1) :=
            hmin (n + 1) (by omega)
          have hmul₁ : 4 * O.value n ≤ 4 * O.value (n + 1) :=
            Nat.mul_le_mul_left 4 hnext
          have hmul₂ :
              4 * O.value (n + 1) ≤
                2 ^ O.exponent n * O.value (n + 1) :=
            Nat.mul_le_mul_right (O.value (n + 1)) hpow
          have hbound : 4 * O.value n ≤ 3 * O.value n + 1 := by
            calc
              4 * O.value n ≤ 4 * O.value (n + 1) := hmul₁
              _ ≤ 2 ^ O.exponent n * O.value (n + 1) := hmul₂
              _ = 3 * O.value n + 1 := O.step n
          omega

/-- future-minimum位置を単調に列挙するデータ。 -/
structure FutureMinimumSequence (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  futureMinimum : ∀ j, O.FutureMinimumAt (index j)
  value_strict : StrictMono (fun j => O.value (index j))
  eventually_large :
    ∀ M J : ℕ, ∃ j : ℕ,
      J ≤ j ∧ M < O.value (index j)

namespace FutureMinimumSequence

/-- 列に沿った軌道値は非有界である。 -/
theorem values_unbounded {O : OddOrbit}
    (S : FutureMinimumSequence O) :
    ∀ M : ℕ, ∃ j : ℕ, M < O.value (S.index j) := by
  intro M
  obtain ⟨j, _, hj⟩ := S.eventually_large M 0
  exact ⟨j, hj⟩

end FutureMinimumSequence

end OddOrbit
end CollatzSecondLayer
