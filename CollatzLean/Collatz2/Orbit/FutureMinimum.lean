import CollatzLean.Collatz2.Orbit.OddOrbit
import Mathlib.Data.Finset.Basic

/-!
# Collatz2: future minima

future minimum は無限軌道上の order property としてのみ定義する。
選択方法は次ファイルへ隔離する。

非有界 normalized odd-only 軌道では step の odd-normalization 一意性から
値の再訪がなく、従って future-minimum 値は strict に増加できる。
-/

namespace Collatz2
namespace OddOrbit

/-- 位置 `n` の値が、その後の全軌道値以下。 -/
def FutureMinimumAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

/-- future minimum から始まる segment の終点は開始値以上。 -/
theorem FutureMinimumAt.le_segment_end
    {O : OddOrbit} {n : ℕ}
    (h : O.FutureMinimumAt n)
    (m : ℕ) :
    O.value n ≤ O.value (n + m) :=
  h _ (by omega)

/-
同じ正整数の normalized 2-adic 分解の一意性。
global orbit の deterministic 性に必要な最小限だけをここで再証明する。
-/

private lemma odd_even_false
    {n : ℕ}
    (ho : Odd n)
    (he : Even n) :
    False := by
  rcases ho with ⟨a, ha⟩
  rcases he with ⟨b, hb⟩
  omega

private lemma even_two_pow_succ_mul
    (r v : ℕ) :
    Even (2 ^ (r + 1) * v) := by
  refine ⟨2 ^ r * v, ?_⟩
  rw [pow_succ]
  ring

private lemma oddPart_eq_twoPow_mul_of_lt
    {a b u v : ℕ}
    (hpow : 2 ^ a * u = 2 ^ b * v)
    (hab : a < b) :
    ∃ r : ℕ, u = 2 ^ (r + 1) * v := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, b = a + (r + 1) := by
    exact ⟨b - a - 1, by omega⟩
  refine ⟨r, ?_⟩
  have hc :
      2 ^ a * u =
        2 ^ a * (2 ^ (r + 1) * v) := by
    calc
      2 ^ a * u = 2 ^ b * v := hpow
      _ = 2 ^ a * (2 ^ (r + 1) * v) := by
        rw [hr, pow_add]
        ring
  exact Nat.mul_left_cancel
    (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hc

/-- 同じ start の normalized odd successor は exponent も next value も一意。 -/
theorem normalizedStep_unique
    {x e₁ e₂ y₁ y₂ : ℕ}
    (h₁ : 2 ^ e₁ * y₁ = 3 * x + 1)
    (h₂ : 2 ^ e₂ * y₂ = 3 * x + 1)
    (hy₁ : Odd y₁)
    (hy₂ : Odd y₂) :
    e₁ = e₂ ∧ y₁ = y₂ := by
  have hpow :
      2 ^ e₁ * y₁ = 2 ^ e₂ * y₂ :=
    h₁.trans h₂.symm
  have he : e₁ = e₂ := by
    have hnot₁₂ : ¬ e₁ < e₂ := by
      intro hlt
      obtain ⟨r, hyr⟩ :=
        oddPart_eq_twoPow_mul_of_lt hpow hlt
      exact odd_even_false hy₁
        (by
          rw [hyr]
          exact even_two_pow_succ_mul r y₂)
    have hnot₂₁ : ¬ e₂ < e₁ := by
      intro hlt
      obtain ⟨r, hyr⟩ :=
        oddPart_eq_twoPow_mul_of_lt hpow.symm hlt
      exact odd_even_false hy₂
        (by
          rw [hyr]
          exact even_two_pow_succ_mul r y₁)
    omega
  have hy : y₁ = y₂ := by
    subst e₂
    exact Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hpow
  exact ⟨he, hy⟩

/-- 二位置で値が一致すれば、その後の normalized value 列も一致する。 -/
theorem value_eq_propagates
    (O : OddOrbit) {n m : ℕ}
    (h : O.value n = O.value m) :
    ∀ k : ℕ, O.value (n + k) = O.value (m + k) := by
  intro k
  induction k with
  | zero =>
      simpa using h
  | succ k ih =>
      have h₁ :
          2 ^ O.exponent (n + k) * O.value (n + k + 1) =
            3 * O.value (n + k) + 1 := by
        simpa [Nat.add_assoc] using O.step (n + k)
      have h₂ :
          2 ^ O.exponent (m + k) * O.value (m + k + 1) =
            3 * O.value (n + k) + 1 := by
        calc
          2 ^ O.exponent (m + k) * O.value (m + k + 1)
              = 3 * O.value (m + k) + 1 := by
                  simpa [Nat.add_assoc] using O.step (m + k)
          _ = 3 * O.value (n + k) + 1 := by rw [ih]
      have hu :=
        normalizedStep_unique
          h₁ h₂
          (O.value_odd (n + k + 1))
          (O.value_odd (m + k + 1))
      simpa [Nat.add_assoc] using hu.2

/-- 二位置の一致から周期差だけ一段後退できる。 -/
theorem value_eq_sub_period
    (O : OddOrbit)
    {n m t : ℕ}
    (hnm : n < m)
    (h : O.value n = O.value m)
    (ht : m ≤ t) :
    O.value t = O.value (t - (m - n)) := by
  let k := t - m
  have htm : t = m + k := by
    dsimp [k]
    omega
  have hnk : t - (m - n) = n + k := by
    dsimp [k]
    omega
  have hp :
      O.value (n + k) = O.value (m + k) :=
    O.value_eq_propagates h k
  calc
    O.value t = O.value (m + k) := by rw [htm]
    _ = O.value (n + k) := hp.symm
    _ = O.value (t - (m - n)) := by rw [hnk]

/-- 非有界軌道は異なる時刻で同じ値を再訪しない。 -/
theorem value_ne_of_lt_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded)
    {n m : ℕ}
    (hlt : n < m) :
    O.value n ≠ O.value m := by
  intro hnm
  let d := m - n
  let B := Finset.sum (Finset.range m) (fun i => O.value i)
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hbound : ∀ t : ℕ, O.value t ≤ B := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        by_cases htm : t < m
        · dsimp [B]
          exact Finset.single_le_sum
            (fun i _ => Nat.zero_le (O.value i))
            (Finset.mem_range.mpr htm)
        · have hmt : m ≤ t := Nat.le_of_not_gt htm
          have hsub : t - d < t := by
            apply Nat.sub_lt
            · omega
            · exact hd
          rw [O.value_eq_sub_period hlt hnm hmt]
          exact ih (t - d) hsub
  obtain ⟨t, ht⟩ := hU B
  exact Nat.not_lt_of_ge (hbound t) ht

/-- 非有界軌道では value 列は単射。 -/
theorem value_injective_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    Function.Injective O.value := by
  intro n m hnm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim
      ((O.value_ne_of_lt_of_unbounded hU hlt) hnm)
  · exact heq
  · exact False.elim
      ((O.value_ne_of_lt_of_unbounded hU hgt) hnm.symm)

/-- 非有界 normalized orbit は任意の固定上界から最終的に脱出する。 -/
theorem escapesToInfinity_of_unbounded
    (O : OddOrbit)
    (hU : O.Unbounded) :
    O.EscapesToInfinity := by
  intro M
  have hinj := O.value_injective_of_unbounded hU
  let Bad := {n : ℕ // O.value n ≤ M}
  let toFin : Bad → Fin (M + 1) :=
    fun n => ⟨O.value n.1, Nat.lt_succ_of_le n.2⟩
  have htoFin : Function.Injective toFin := by
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact congrArg Fin.val hab
  letI : Finite Bad := Finite.of_injective toFin htoFin
  letI : Fintype Bad := Fintype.ofFinite Bad
  let N : ℕ :=
    Finset.sum Finset.univ (fun x : Bad => x.1 + 1)
  refine ⟨N, ?_⟩
  intro n hn
  by_contra hnot
  have hbad : O.value n ≤ M := Nat.le_of_not_gt hnot
  let x : Bad := ⟨n, hbad⟩
  have hx : n + 1 ≤ N := by
    dsimp [N]
    simpa [x] using
      (Finset.single_le_sum
        (fun y (_ : y ∈ (Finset.univ : Finset Bad)) =>
          Nat.zero_le (y.1 + 1))
        (Finset.mem_univ x))
  omega

/--
選択済み future-minimum 列。
選択方法そのものは保持せず、下流で必要な order 情報だけを lossless に渡す。
-/
structure FutureMinima (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  minimum : ∀ j, O.FutureMinimumAt (index j)
  value_strict : StrictMono (fun j => O.value (index j))
  eventually_large :
    ∀ M J : ℕ, ∃ j : ℕ, J ≤ j ∧ M < O.value (index j)

namespace FutureMinima

/-- strict index 列は添字自身以上。 -/
theorem index_ge
    {O : OddOrbit}
    (S : O.FutureMinima)
    (j : ℕ) :
    j ≤ S.index j := by
  induction j with
  | zero =>
      exact Nat.zero_le _
  | succ j ih =>
      have hlt :
          S.index j < S.index j.succ :=
        S.index_strict (Nat.lt_succ_self j)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- future-minimum 値は最終的に任意の上界を越える。 -/
theorem values_eventually_large
    {O : OddOrbit}
    (S : O.FutureMinima)
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < O.value (S.index j) := by
  obtain ⟨J, _, hJ⟩ := S.eventually_large M 0
  refine ⟨J, ?_⟩
  intro j hj
  exact lt_of_lt_of_le hJ (S.value_strict.monotone hj)

end FutureMinima
end OddOrbit
end Collatz2
