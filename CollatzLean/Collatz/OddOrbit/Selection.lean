import CollatzLean.Collatz.OddOrbit.FutureMinimum

/-!
# 標準future-minimum選択

無限tailから代表を選ぶ操作だけを`noncomputable`として隔離する。
選択後の`FutureMinima`は通常の明示データとして下流へ渡す。
-/

namespace Collatz
namespace OddOrbit
namespace Selection

/-- tail以後に現れる値は少なくとも一つある。 -/
theorem exists_tail_value (O : OddOrbit) (N : ℕ) :
    ∃ v : ℕ, ∃ n : ℕ, N ≤ n ∧ O.value n = v :=
  ⟨O.value N, N, le_rfl, rfl⟩

/-- tail最小値。 -/
noncomputable def tailMinValue (O : OddOrbit) (N : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_tail_value O N)

/-- tail最小値を実現する位置。 -/
noncomputable def tailMinIndex (O : OddOrbit) (N : ℕ) : ℕ := by
  classical
  exact Classical.choose (Nat.find_spec (exists_tail_value O N))

/-- tail minimum indexは閾値以後。 -/
theorem tailMinIndex_ge (O : OddOrbit) (N : ℕ) :
    N ≤ tailMinIndex O N := by
  classical
  exact (Classical.choose_spec (Nat.find_spec (exists_tail_value O N))).1

/-- tail minimum indexの値。 -/
theorem value_tailMinIndex (O : OddOrbit) (N : ℕ) :
    O.value (tailMinIndex O N) = tailMinValue O N := by
  classical
  exact (Classical.choose_spec (Nat.find_spec (exists_tail_value O N))).2

/-- tail最小値はtail中の任意の値以下。 -/
theorem tailMinValue_le
    (O : OddOrbit) (N m : ℕ) (hm : N ≤ m) :
    tailMinValue O N ≤ O.value m := by
  classical
  unfold tailMinValue
  exact Nat.find_min' (exists_tail_value O N) ⟨m, hm, rfl⟩

/-- 選んだtail minimumはfuture minimum。 -/
theorem futureMinimumAt_tailMinIndex (O : OddOrbit) (N : ℕ) :
    O.FutureMinimumAt (tailMinIndex O N) := by
  intro m hm
  rw [value_tailMinIndex]
  exact tailMinValue_le O N m (le_trans (tailMinIndex_ge O N) hm)

/-- tail minimumを再帰的に選ぶ標準位置列。 -/
noncomputable def futureMinIndex (O : OddOrbit) : ℕ → ℕ
  | 0 => tailMinIndex O 0
  | j + 1 => tailMinIndex O (futureMinIndex O j + 1)

/-- 標準位置列は一段ごとに増える。 -/
theorem futureMinIndex_lt_succ (O : OddOrbit) (j : ℕ) :
    futureMinIndex O j < futureMinIndex O (j + 1) := by
  rw [futureMinIndex]
  have h := tailMinIndex_ge O (futureMinIndex O j + 1)
  omega

/-- 標準位置列は狭義単調。 -/
theorem futureMinIndex_strict (O : OddOrbit) :
    StrictMono (futureMinIndex O) :=
  strictMono_nat_of_lt_succ (futureMinIndex_lt_succ O)

/-- 標準位置はfuture minimum。 -/
theorem futureMinimumAt_futureMinIndex (O : OddOrbit) (j : ℕ) :
    O.FutureMinimumAt (futureMinIndex O j) := by
  cases j with
  | zero => simpa [futureMinIndex] using futureMinimumAt_tailMinIndex O 0
  | succ j => simpa [futureMinIndex] using
      futureMinimumAt_tailMinIndex O (futureMinIndex O j + 1)

/-- 非有界軌道では標準future-minimum値も真に増える。 -/
theorem futureMinValue_lt_succ
    (O : OddOrbit) (hU : O.Unbounded) (j : ℕ) :
    O.value (futureMinIndex O j) < O.value (futureMinIndex O (j + 1)) := by
  have hle :=
    (futureMinimumAt_futureMinIndex O j)
      (futureMinIndex O (j + 1))
      (Nat.le_of_lt (futureMinIndex_lt_succ O j))
  have hne :
      O.value (futureMinIndex O j) ≠
        O.value (futureMinIndex O (j + 1)) := by
    intro hEq
    exact
      (Nat.ne_of_lt (futureMinIndex_lt_succ O j))
        (O.value_injective_of_unbounded hU hEq)
  omega

/-- 標準future-minimum列を選択済みデータとして構成。 -/
noncomputable def futureMinima
    (O : OddOrbit) (hU : O.Unbounded) : O.FutureMinima where
  index := futureMinIndex O
  index_strict := futureMinIndex_strict O
  minimum := futureMinimumAt_futureMinIndex O
  value_strict :=
    strictMono_nat_of_lt_succ (futureMinValue_lt_succ O hU)
  eventually_large := by
    intro M J
    obtain ⟨N, hN⟩ := O.escapesToInfinity_of_unbounded hU M
    let j := N + J
    refine ⟨j, by omega, ?_⟩
    apply hN
    have hj : j ≤ futureMinIndex O j := by
      induction j with
      | zero =>
          exact Nat.zero_le _
      | succ j ih =>
          have hlt :
              futureMinIndex O j < futureMinIndex O (j + 1) :=
            futureMinIndex_strict O (Nat.lt_succ_self j)
          omega
    exact le_trans (by omega : N ≤ j) hj

end Selection
end OddOrbit
end Collatz
