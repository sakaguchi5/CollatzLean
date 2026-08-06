import CollatzLean.CollatzOrbitCore.InfiniteOrbit
import CollatzLean.CollatzFirstLayer.FirstCarry

import Mathlib.Data.Finset.Basic

/-!
# future-minimum列

非有界odd-only軌道から、後続tail全体の最小値を再帰的に選ぶ。
旧SecondLayerのmoving compactnessより前に必要だった基礎を独立に再構成する。
-/

namespace CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- 位置`n`の値が、その後のすべての軌道値以下であること。 -/
def FutureMinimumAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

/-- future-minimumから始まる有限segmentの終点は開始値以上。 -/
theorem futureMinimum_le_segment_end
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n) (m : ℕ) :
    O.value n ≤ O.value (n + m) :=
  hmin (n + m) (by omega)

/-- 同じ奇数から始まるodd-only一段の指数と次値は一意。 -/
theorem next_data_unique
    {x e₁ e₂ y₁ y₂ : ℕ}
    (h₁ : 2 ^ e₁ * y₁ = 3 * x + 1)
    (h₂ : 2 ^ e₂ * y₂ = 3 * x + 1)
    (hy₁ : Odd y₁) (hy₂ : Odd y₂) :
    e₁ = e₂ ∧ y₁ = y₂ := by
  have hfac₁ : ExactTwoFactor (3 * x + 1) e₁ y₁ :=
    ⟨h₁.symm, hy₁⟩
  have hfac₂ : ExactTwoFactor (3 * x + 1) e₂ y₂ :=
    ⟨h₂.symm, hy₂⟩
  exact exactTwoFactor_unique hfac₁ hfac₂

/-- 二位置で値が一致すれば、その後の値列も一致する。 -/
theorem value_eq_propagates
    (O : OddOrbit) {n m : ℕ}
    (h : O.value n = O.value m) :
    ∀ k : ℕ, O.value (n + k) = O.value (m + k) := by
  intro k
  induction k with
  | zero => simpa using h
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
      have hu := next_data_unique h₁ h₂
          (O.value_odd (n + k + 1))
          (O.value_odd (m + k + 1))
      simpa [Nat.add_assoc] using hu.2

/-- 二位置の一致から、周期差だけ一段後退できる。 -/
theorem value_eq_sub_period
    (O : OddOrbit) {n m t : ℕ}
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
  have hp : O.value (n + k) = O.value (m + k) :=
    O.value_eq_propagates h k
  calc
    O.value t = O.value (m + k) := by rw [htm]
    _ = O.value (n + k) := hp.symm
    _ = O.value (t - (m - n)) := by rw [hnk]

/-- 非有界軌道は後方で同じ値を再訪しない。 -/
theorem value_ne_of_lt_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded)
    {n m : ℕ} (hlt : n < m) :
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

/-- 非有界軌道では値列は単射。 -/
theorem value_injective_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    Function.Injective O.value := by
  intro n m hnm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hlt) hnm)
  · exact heq
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hgt) hnm.symm)

/-- 非有界軌道は任意の固定上界から最終的に脱出する。 -/
theorem escapesToInfinity_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) :
    O.EscapesToInfinity := by
  intro M
  have hinj : Function.Injective O.value :=
    O.value_injective_of_unbounded hU
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
  let N : ℕ := Finset.sum Finset.univ (fun x : Bad => x.1 + 1)
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

/-- 閾値以後の軌道値は少なくとも一つ存在する。 -/
theorem exists_tail_value (O : OddOrbit) (N : ℕ) :
    ∃ v : ℕ, ∃ n : ℕ, N ≤ n ∧ O.value n = v :=
  ⟨O.value N, N, le_rfl, rfl⟩

/-- 閾値以後に現れる最小値。 -/
noncomputable def tailMinValue (O : OddOrbit) (N : ℕ) : ℕ := by
  classical
  exact Nat.find (O.exists_tail_value N)

/-- tail最小値は実際に軌道上で実現される。 -/
theorem tailMinValue_spec (O : OddOrbit) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ O.value n = O.tailMinValue N := by
  classical
  unfold tailMinValue
  exact Nat.find_spec (O.exists_tail_value N)

/-- tail最小値を実現する位置を一つ選ぶ。 -/
noncomputable def tailMinIndex (O : OddOrbit) (N : ℕ) : ℕ :=
  Classical.choose (O.tailMinValue_spec N)

@[simp] theorem tailMinIndex_ge (O : OddOrbit) (N : ℕ) :
    N ≤ O.tailMinIndex N :=
  (Classical.choose_spec (O.tailMinValue_spec N)).1

@[simp] theorem value_tailMinIndex (O : OddOrbit) (N : ℕ) :
    O.value (O.tailMinIndex N) = O.tailMinValue N :=
  (Classical.choose_spec (O.tailMinValue_spec N)).2

/-- tail最小値は閾値以後の任意の値以下。 -/
theorem tailMinValue_le
    (O : OddOrbit) (N m : ℕ) (hm : N ≤ m) :
    O.tailMinValue N ≤ O.value m := by
  classical
  unfold tailMinValue
  exact Nat.find_min' (O.exists_tail_value N) ⟨m, hm, rfl⟩

/-- tail最小位置はfuture-minimum。 -/
theorem futureMinimumAt_tailMinIndex
    (O : OddOrbit) (N : ℕ) :
    O.FutureMinimumAt (O.tailMinIndex N) := by
  intro m hm
  rw [O.value_tailMinIndex]
  exact O.tailMinValue_le N m
    (le_trans (O.tailMinIndex_ge N) hm)

/-- tail最小位置を再帰的に選び続ける。 -/
noncomputable def futureMinIndex (O : OddOrbit) : ℕ → ℕ
  | 0 => O.tailMinIndex 0
  | j + 1 => O.tailMinIndex (O.futureMinIndex j + 1)

/-- future-minimum位置は一段ごとに真に増える。 -/
theorem futureMinIndex_lt_succ (O : OddOrbit) (j : ℕ) :
    O.futureMinIndex j < O.futureMinIndex (j + 1) := by
  rw [futureMinIndex]
  have h := O.tailMinIndex_ge (O.futureMinIndex j + 1)
  omega

/-- future-minimum位置列は狭義単調。 -/
theorem futureMinIndex_strict (O : OddOrbit) :
    StrictMono O.futureMinIndex :=
  strictMono_nat_of_lt_succ O.futureMinIndex_lt_succ

/-- 列添字は対応する軌道位置以下。 -/
theorem index_le_futureMinIndex (O : OddOrbit) :
    ∀ j : ℕ, j ≤ O.futureMinIndex j := by
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
      have hs := O.futureMinIndex_lt_succ j
      omega

/-- 再帰的に選んだ各位置はfuture-minimum。 -/
theorem futureMinimumAt_futureMinIndex (O : OddOrbit) (j : ℕ) :
    O.FutureMinimumAt (O.futureMinIndex j) := by
  cases j with
  | zero =>
      simpa [futureMinIndex] using O.futureMinimumAt_tailMinIndex 0
  | succ j =>
      simpa [futureMinIndex] using
        O.futureMinimumAt_tailMinIndex (O.futureMinIndex j + 1)

/-- 非有界軌道ではfuture-minimum値列も真に増える。 -/
theorem futureMinValue_lt_succ
    (O : OddOrbit) (hU : O.Unbounded) (j : ℕ) :
    O.value (O.futureMinIndex j) <
      O.value (O.futureMinIndex (j + 1)) := by
  have hle :=
    (O.futureMinimumAt_futureMinIndex j)
      (O.futureMinIndex (j + 1))
      (Nat.le_of_lt (O.futureMinIndex_lt_succ j))
  have hne :
      O.value (O.futureMinIndex j) ≠
        O.value (O.futureMinIndex (j + 1)) := by
    apply O.value_ne_of_lt_of_unbounded hU
    exact O.futureMinIndex_lt_succ j
  omega

/-- future-minimum列をまとめたデータ。 -/
structure FutureMinimumSequence (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  futureMinimum : ∀ j, O.FutureMinimumAt (index j)
  value_strict : StrictMono (fun j => O.value (index j))
  eventually_large :
    ∀ M J : ℕ, ∃ j : ℕ,
      J ≤ j ∧ M < O.value (index j)

/-- 非有界軌道から標準future-minimum列を構成する。 -/
noncomputable def futureMinimumSequence
    (O : OddOrbit) (hU : O.Unbounded) :
    O.FutureMinimumSequence where
  index := O.futureMinIndex
  index_strict := O.futureMinIndex_strict
  futureMinimum := O.futureMinimumAt_futureMinIndex
  value_strict := strictMono_nat_of_lt_succ (O.futureMinValue_lt_succ hU)
  eventually_large := by
    intro M J
    obtain ⟨N, hN⟩ := O.escapesToInfinity_of_unbounded hU M
    let j := N + J
    refine ⟨j, by omega, ?_⟩
    apply hN
    exact le_trans (by omega : N ≤ j) (O.index_le_futureMinIndex j)

namespace FutureMinimumSequence

/-- future-minimum値は任意の上界を最終的に越える。 -/
theorem values_eventually_large
    {O : OddOrbit} (S : O.FutureMinimumSequence) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < O.value (S.index j) := by
  intro M
  obtain ⟨J, _, hJ⟩ := S.eventually_large M 0
  refine ⟨J, ?_⟩
  intro j hj
  exact lt_of_lt_of_le hJ (S.value_strict.monotone hj)

end FutureMinimumSequence

end OddOrbit
end CollatzCore
