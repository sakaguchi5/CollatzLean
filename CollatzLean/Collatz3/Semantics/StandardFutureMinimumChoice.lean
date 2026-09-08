import CollatzLean.Collatz3.Semantics.StandardFutureMinimum

/-!
# Collatz3: classical choice による標準 future-minimum 列

このファイルは **optional classical layer** である。

無限 tail 全体の最小値と、その最小値を実現する位置を classical choice で一つ選び、
標準 future-minimum 列の具体的 witness を構成する。

重要:

* `StandardFutureMinimum.lean` の stable API は `FutureMinima.IsStandard` だけを要求する。
* このファイルの constructor は計算用 API ではない。
* `Collatz3.lean` からは import しない。

したがって後段の数学は noncomputable な canonical selector に依存せず、
必要な場合だけこのファイルを import して標準列の存在 witness を得られる。
-/

namespace Collatz3
namespace OddOrbit

/-- 閾値 `N` 以後に現れる値は少なくとも一つ存在する。 -/
theorem exists_tail_value
    (O : OddOrbit)
    (N : ℕ) :
    ∃ v : ℕ, ∃ n : ℕ, N ≤ n ∧ O.value n = v :=
  ⟨O.value N, N, le_rfl, rfl⟩

/--
閾値 `N` 以後に現れる最小値。
無限 tail 全体に対する最小化なので stable computable API には置かない。
-/
noncomputable def tailMinValue
    (O : OddOrbit)
    (N : ℕ) : ℕ := by
  classical
  exact Nat.find (O.exists_tail_value N)

/-- tail minimum value は実際の軌道位置で実現される。 -/
theorem tailMinValue_spec
    (O : OddOrbit)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ O.value n = O.tailMinValue N := by
  classical
  unfold tailMinValue
  exact Nat.find_spec (O.exists_tail_value N)

/-- tail minimum value を実現する位置を classical に一つ選ぶ。 -/
noncomputable def tailMinIndex
    (O : OddOrbit)
    (N : ℕ) : ℕ :=
  Classical.choose (O.tailMinValue_spec N)

@[simp] theorem tailMinIndex_ge
    (O : OddOrbit)
    (N : ℕ) :
    N ≤ O.tailMinIndex N :=
  (Classical.choose_spec (O.tailMinValue_spec N)).1

@[simp] theorem value_tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    O.value (O.tailMinIndex N) = O.tailMinValue N :=
  (Classical.choose_spec (O.tailMinValue_spec N)).2

/-- tail minimum value は閾値以後の任意の軌道値以下。 -/
theorem tailMinValue_le
    (O : OddOrbit)
    (N m : ℕ)
    (hm : N ≤ m) :
    O.tailMinValue N ≤ O.value m := by
  classical
  unfold tailMinValue
  exact Nat.find_min' (O.exists_tail_value N) ⟨m, hm, rfl⟩

/-- 選択した tail minimum 位置は future minimum。 -/
theorem futureMinimumAt_tailMinIndex
    (O : OddOrbit)
    (N : ℕ) :
    O.FutureMinimumAt (O.tailMinIndex N) := by
  intro m hm
  rw [O.value_tailMinIndex]
  exact O.tailMinValue_le N m
    (le_trans (O.tailMinIndex_ge N) hm)

/-- tail minimum を current+1 以後から再帰的に選ぶ classical canonical index 列。 -/
noncomputable def standardFutureMinIndex
    (O : OddOrbit) : ℕ → ℕ
  | 0 => O.tailMinIndex 0
  | j + 1 => O.tailMinIndex (O.standardFutureMinIndex j + 1)

/-- canonical index は一段ごとに strict に進む。 -/
theorem standardFutureMinIndex_lt_succ
    (O : OddOrbit)
    (j : ℕ) :
    O.standardFutureMinIndex j <
      O.standardFutureMinIndex (j + 1) := by
  rw [standardFutureMinIndex]
  have h := O.tailMinIndex_ge (O.standardFutureMinIndex j + 1)
  omega

/-- canonical index 列は strict monotone。 -/
theorem standardFutureMinIndex_strict
    (O : OddOrbit) :
    StrictMono O.standardFutureMinIndex :=
  strictMono_nat_of_lt_succ O.standardFutureMinIndex_lt_succ

/-- canonical に選んだ各 index は future minimum。 -/
theorem futureMinimumAt_standardFutureMinIndex
    (O : OddOrbit)
    (j : ℕ) :
    O.FutureMinimumAt (O.standardFutureMinIndex j) := by
  cases j with
  | zero =>
      simpa [standardFutureMinIndex] using
        O.futureMinimumAt_tailMinIndex 0
  | succ j =>
      simpa [standardFutureMinIndex] using
        O.futureMinimumAt_tailMinIndex (O.standardFutureMinIndex j + 1)

/-- classical に選んだ標準 index 列を `FutureMinima` packet にまとめる。 -/
noncomputable def standardFutureMinima
    (O : OddOrbit) : O.FutureMinima where
  index := O.standardFutureMinIndex
  index_strict := O.standardFutureMinIndex_strict
  minimum := O.futureMinimumAt_standardFutureMinIndex

/-- classical canonical selector は stable API の `IsStandard` を満たす。 -/
theorem standardFutureMinima_isStandard
    (O : OddOrbit) :
    (O.standardFutureMinima).IsStandard := by
  intro j t hjt
  change O.standardFutureMinIndex j < t at hjt
  change
    O.value (O.standardFutureMinIndex (j + 1)) ≤
      O.value t
  rw [standardFutureMinIndex, O.value_tailMinIndex]
  exact
    O.tailMinValue_le
      (O.standardFutureMinIndex j + 1)
      t
      (Nat.succ_le_of_lt hjt)

/--
標準 future-minimum 列は classical に少なくとも一つ存在する。
後段はこの存在定理から witness を取るより、通常は `S` と `S.IsStandard` を仮定して使う。
-/
theorem exists_standardFutureMinima
    (O : OddOrbit) :
    ∃ S : O.FutureMinima, S.IsStandard :=
  ⟨O.standardFutureMinima, O.standardFutureMinima_isStandard⟩

end OddOrbit
end Collatz3
