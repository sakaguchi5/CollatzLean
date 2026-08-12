import CollatzLean.Collatz2.Orbit.FutureMinimum

/-!
# Collatz2: future-minimum selection

無限 tail から minimum representative を選ぶ noncomputable 操作だけを隔離する。
下流は選択手続きではなく `FutureMinima` の保持する性質だけを見る。
-/

namespace Collatz2
namespace OddOrbit
namespace FutureMinimumSelection

/-- tail 以後に現れる値は少なくとも一つある。 -/
theorem exists_tail_value
    (O : OddOrbit)
    (N : ℕ) :
    ∃ v : ℕ, ∃ n : ℕ, N ≤ n ∧ O.value n = v :=
  ⟨O.value N, N, le_rfl, rfl⟩

/-- tail の最小値。 -/
noncomputable def tailMinValue
    (O : OddOrbit)
    (N : ℕ) :
    ℕ := by
  classical
  exact Nat.find (exists_tail_value O N)

/-- tail 最小値を実現する位置。 -/
noncomputable def tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    ℕ := by
  classical
  exact Classical.choose
    (Nat.find_spec (exists_tail_value O N))

/-- 選択位置は threshold 以後。 -/
theorem tailMinIndex_ge
    (O : OddOrbit)
    (N : ℕ) :
    N ≤ tailMinIndex O N := by
  classical
  exact
    (Classical.choose_spec
      (Nat.find_spec (exists_tail_value O N))).1

/-- 選択位置の値は tail minimum。 -/
theorem value_tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    O.value (tailMinIndex O N) = tailMinValue O N := by
  classical
  exact
    (Classical.choose_spec
      (Nat.find_spec (exists_tail_value O N))).2

/-- tail minimum は tail 中の任意の値以下。 -/
theorem tailMinValue_le
    (O : OddOrbit)
    (N m : ℕ)
    (hm : N ≤ m) :
    tailMinValue O N ≤ O.value m := by
  classical
  unfold tailMinValue
  exact Nat.find_min'
    (exists_tail_value O N)
    ⟨m, hm, rfl⟩

/-- 選んだ tail minimum は future minimum。 -/
theorem futureMinimumAt_tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    O.FutureMinimumAt (tailMinIndex O N) := by
  intro m hm
  rw [value_tailMinIndex]
  exact tailMinValue_le O N m
    (le_trans (tailMinIndex_ge O N) hm)

/-- tail minimum を一つ先から再帰的に選ぶ標準位置列。 -/
noncomputable def futureMinIndex
    (O : OddOrbit) :
    ℕ → ℕ
  | 0 => tailMinIndex O 0
  | j + 1 => tailMinIndex O (futureMinIndex O j + 1)

/-- 選択位置列は一段ごとに strict に進む。 -/
theorem futureMinIndex_lt_succ
    (O : OddOrbit)
    (j : ℕ) :
    futureMinIndex O j < futureMinIndex O (j + 1) := by
  rw [futureMinIndex]
  have h :=
    tailMinIndex_ge O (futureMinIndex O j + 1)
  omega

/-- 選択位置列は StrictMono。 -/
theorem futureMinIndex_strict
    (O : OddOrbit) :
    StrictMono (futureMinIndex O) :=
  strictMono_nat_of_lt_succ (futureMinIndex_lt_succ O)

/-- 各選択位置は future minimum。 -/
theorem futureMinimumAt_futureMinIndex
    (O : OddOrbit)
    (j : ℕ) :
    O.FutureMinimumAt (futureMinIndex O j) := by
  cases j with
  | zero =>
      simpa [futureMinIndex] using
        futureMinimumAt_tailMinIndex O 0
  | succ j =>
      simpa [futureMinIndex] using
        futureMinimumAt_tailMinIndex O
          (futureMinIndex O j + 1)

/-- 非有界軌道では隣接 future-minimum 値も strict に増える。 -/
theorem futureMinValue_lt_succ
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) :
    O.value (futureMinIndex O j) <
      O.value (futureMinIndex O (j + 1)) := by
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

/--
非有界軌道から選択済み `FutureMinima` を構成する。
下流ではこの selection 実装を参照する必要はない。
-/
noncomputable def futureMinima
    (O : OddOrbit)
    (hU : O.Unbounded) :
    O.FutureMinima where
  index := futureMinIndex O
  index_strict := futureMinIndex_strict O
  minimum := futureMinimumAt_futureMinIndex O
  value_strict :=
    strictMono_nat_of_lt_succ
      (futureMinValue_lt_succ O hU)
  eventually_large := by
    intro M J
    obtain ⟨N, hN⟩ :=
      O.escapesToInfinity_of_unbounded hU M
    let j := N + J
    refine ⟨j, by omega, ?_⟩
    apply hN
    have hj : j ≤ futureMinIndex O j := by
      induction j with
      | zero =>
          exact Nat.zero_le _
      | succ j ih =>
          have hlt :
              futureMinIndex O j <
                futureMinIndex O (j + 1) :=
            futureMinIndex_strict O
              (Nat.lt_succ_self j)
          omega
    exact le_trans (by omega : N ≤ j) hj

end FutureMinimumSelection
end OddOrbit
end Collatz2
