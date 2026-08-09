import CollatzLean.Collatz.OddOrbit.Basic
import CollatzLean.Collatz.OneStep.Carry
import Mathlib.Data.Finset.Basic

/-!
# future minimumの性質

ここではfuture minimumという性質だけを扱い、標準列の選択は別ファイルへ隔離する。
-/

namespace Collatz
namespace OddOrbit

/-- 位置`n`の値が、その後の全軌道値以下。 -/
def FutureMinimumAt (O : OddOrbit) (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

/-- future minimumから始まるsegmentの終点は開始値以上。 -/
theorem FutureMinimumAt.le_segment_end
    {O : OddOrbit} {n : ℕ}
    (h : O.FutureMinimumAt n) (m : ℕ) :
    O.value n ≤ O.value (n + m) := h _ (by omega)

/-- 二位置で値が一致すれば、その後の値列も一致。 -/
theorem value_eq_propagates
    (O : OddOrbit) {n m : ℕ}
    (h : O.value n = O.value m) :
    ∀ k : ℕ, O.value (n + k) = O.value (m + k) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have h₁ : 2 ^ O.exponent (n + k) * O.value (n + k + 1) =
          3 * O.value (n + k) + 1 := by simpa [Nat.add_assoc] using O.step (n + k)
      have h₂ : 2 ^ O.exponent (m + k) * O.value (m + k + 1) =
          3 * O.value (n + k) + 1 := by
        calc
          2 ^ O.exponent (m + k) * O.value (m + k + 1)
              = 3 * O.value (m + k) + 1 := by simpa [Nat.add_assoc] using O.step (m + k)
          _ = 3 * O.value (n + k) + 1 := by rw [ih]
      have hu := OneStep.next_unique h₁ h₂
        (O.value_odd (n + k + 1)) (O.value_odd (m + k + 1))
      simpa [Nat.add_assoc] using hu.2

/-- 二位置の一致から周期差だけ一段後退できる。 -/
theorem value_eq_sub_period
    (O : OddOrbit) {n m t : ℕ}
    (hnm : n < m)
    (h : O.value n = O.value m)
    (ht : m ≤ t) :
    O.value t = O.value (t - (m - n)) := by
  let k := t - m
  have htm : t = m + k := by dsimp [k]; omega
  have hnk : t - (m - n) = n + k := by dsimp [k]; omega
  have hp : O.value (n + k) = O.value (m + k) := O.value_eq_propagates h k
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
  have hd : 0 < d := by dsimp [d]; omega
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
    (O : OddOrbit) (hU : O.Unbounded) : Function.Injective O.value := by
  intro n m hnm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hlt) hnm)
  · exact heq
  · exact False.elim ((O.value_ne_of_lt_of_unbounded hU hgt) hnm.symm)

/-- 非有界軌道は任意の固定上界から最終的に脱出する。 -/
theorem escapesToInfinity_of_unbounded
    (O : OddOrbit) (hU : O.Unbounded) : O.EscapesToInfinity := by
  intro M
  have hinj := O.value_injective_of_unbounded hU
  let Bad := {n : ℕ // O.value n ≤ M}
  let toFin : Bad → Fin (M + 1) := fun n => ⟨O.value n.1, Nat.lt_succ_of_le n.2⟩
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
        (fun y (_ : y ∈ (Finset.univ : Finset Bad)) => Nat.zero_le (y.1 + 1))
        (Finset.mem_univ x))
  omega

/-- 選択済みfuture-minimum列。選択方法そのものはこの構造に含めない。 -/
structure FutureMinima (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  minimum : ∀ j, O.FutureMinimumAt (index j)
  value_strict : StrictMono (fun j => O.value (index j))
  eventually_large : ∀ M J : ℕ, ∃ j : ℕ, J ≤ j ∧ M < O.value (index j)

namespace FutureMinima

/-- 選択列の添字は自身以上。 -/
theorem index_ge
    {O : OddOrbit} (S : O.FutureMinima) (j : ℕ) :
    j ≤ S.index j := by
  induction j with
  | zero =>
      exact Nat.zero_le _
  | succ j ih =>
      have hlt :
          S.index j < S.index j.succ :=
        S.index_strict (Nat.lt_succ_self j)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- future-minimum値は最終的に任意の上界を越える。 -/
theorem values_eventually_large
    {O : OddOrbit} (S : O.FutureMinima) (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < O.value (S.index j) := by
  obtain ⟨J, _, hJ⟩ := S.eventually_large M 0
  refine ⟨J, ?_⟩
  intro j hj
  exact lt_of_lt_of_le hJ (S.value_strict.monotone hj)

end FutureMinima
end OddOrbit
end Collatz
