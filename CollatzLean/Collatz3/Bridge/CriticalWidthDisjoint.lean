import CollatzLean.Collatz3.Bridge.CriticalActualClassification

/-!
# Collatz3 Bridge: critical first-passage の幅一意性

固定幅内部では既に restricted partition ごとの actual fiber が pairwise disjoint である。
本ファイルではさらに、異なる幅 `m ≠ n` の actual critical first-passage start も
同じ整数を共有できないことを証明する。

核心は単純である。

* 同じ start から出る二つの actual run は prefix comparable。
* 短い critical word は幅 `m` で terminal depth
  `beattyIndex m + 1` に達している。
* 長い critical word から見ると同じ cut `m` は proper prefix なので
  depth は `beattyIndex m` 以下でなければならない。

従って同じ start が二つの異なる critical width を持つことはできない。
-/

namespace Collatz3
namespace Bridge

/--
幅 `m < n` の二つの critical word は、同じ start から actual run を持てない。
-/
theorem no_common_start_of_critical_width_lt
    {m n x y z : ℕ}
    (hmn : m < n)
    (Wm : Critical.CriticalWord m)
    (Wn : Critical.CriticalWord n)
    (hRunM : Runs Wm.1 x y)
    (hRunN : Runs Wn.1 x z) :
    False := by
  rcases Runs.prefixComparable_of_common_start hRunM hRunN with hLeft | hRight
  · rcases hLeft with ⟨t, hEq, _hSuffix⟩
    have hIndex :
        Word.prefixTwoDepth (Wm.1 ++ t) m =
          Word.prefixTwoDepth (Wm.1 ++ t) (Word.oddSteps Wm.1) := by
      exact congrArg
        (fun j : ℕ => Word.prefixTwoDepth (Wm.1 ++ t) j)
        Wm.2.oddSteps_eq.symm
    have hPrefix :
        Word.prefixTwoDepth Wn.1 m = Word.twoSteps Wm.1 := by
      calc
        Word.prefixTwoDepth Wn.1 m
            = Word.prefixTwoDepth (Wm.1 ++ t) m := by
                rw [hEq]
        _ = Word.prefixTwoDepth
              (Wm.1 ++ t) (Word.oddSteps Wm.1) := hIndex
        _ = Word.twoSteps Wm.1 := by
              unfold Word.prefixTwoDepth
              simp [Word.oddSteps, Word.twoSteps]
    have hmProper : m < Word.oddSteps Wn.1 := by
      rw [Wn.2.oddSteps_eq]
      exact hmn
    have hRoof := Wn.2.prefixTwoDepth_le_beatty  (k := m)
    rw [hPrefix, Wm.2.twoSteps_eq,
      Critical.criticalTwoDepth_eq] at hRoof
    omega
  · rcases hRight with ⟨t, hEq, _hSuffix⟩
    have hSteps := congrArg Word.oddSteps hEq
    rw [Wm.2.oddSteps_eq, Word.oddSteps_append, Wn.2.oddSteps_eq] at hSteps
    omega

/--
同じ start から actual critical trajectory が二つ出るなら、その幅は一致する。
-/
theorem critical_width_eq_of_common_actual_start
    {m n x y z : ℕ}
    (Wm : Critical.CriticalWord m)
    (Wn : Critical.CriticalWord n)
    (hRunM : Runs Wm.1 x y)
    (hRunN : Runs Wn.1 x z) :
    m = n := by
  by_contra hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact no_common_start_of_critical_width_lt hlt Wm Wn hRunM hRunN
  · exact no_common_start_of_critical_width_lt hgt Wn Wm hRunN hRunM

/--
`IsActualCriticalStart` が同じ整数で成立する幅は一意。
-/
theorem actualCriticalStart_width_unique
    {m n x : ℕ}
    (hm : IsActualCriticalStart m x)
    (hn : IsActualCriticalStart n x) :
    m = n := by
  rcases hm with ⟨Wm, y, hRunM⟩
  rcases hn with ⟨Wn, z, hRunN⟩
  exact critical_width_eq_of_common_actual_start Wm Wn hRunM hRunN

/-- 異なる幅の actual critical start 集合は disjoint。 -/
theorem not_actualCriticalStart_both_of_width_ne
    {m n x : ℕ}
    (hmn : m ≠ n) :
    ¬ (IsActualCriticalStart m x ∧ IsActualCriticalStart n x) := by
  rintro ⟨hm, hn⟩
  exact hmn (actualCriticalStart_width_unique hm hn)

/--
異なる幅の partition lift は、partition や lift index に依らず start が一致しない。
-/
theorem liftedCriticalStart_ne_of_width_ne
    {m n : ℕ}
    (hm : 0 < m)
    (hn : 0 < n)
    (hmn : m ≠ n)
    (P : RestrictedCriticalPartition m)
    (Q : RestrictedCriticalPartition n)
    (k l : ℕ) :
    liftedCriticalStart hm P k ≠ liftedCriticalStart hn Q l := by
  intro hEq
  have hStartM :
      IsActualCriticalStart m (liftedCriticalStart hm P k) :=
    (isActualCriticalStart_iff_exists_partition_lift hm).2 ⟨P, k, rfl⟩
  have hStartN :
      IsActualCriticalStart n (liftedCriticalStart hm P k) := by
    rw [hEq]
    exact
      (isActualCriticalStart_iff_exists_partition_lift hn).2
        ⟨Q, l, rfl⟩
  exact hmn (actualCriticalStart_width_unique hStartM hStartN)

/-- positive width の actual critical start は奇数。 -/
theorem isActualCriticalStart_odd_of_pos
    {m x : ℕ}
    (hm : 0 < m)
    (hStart : IsActualCriticalStart m x) :
    Odd x := by
  rcases hStart with ⟨W, y, hRun⟩
  exact hRun.start_odd_of_nonempty (criticalWord_nonempty hm W)

/-- どこかの幅で critical start になるという全幅述語。 -/
def IsAnyActualCriticalStart (x : ℕ) : Prop :=
  ∃ m : ℕ, IsActualCriticalStart m x

/--
全幅をまとめても、各 actual critical start には一意な first-passage 幅がある。
-/
theorem existsUnique_criticalWidth_of_anyStart
    {x : ℕ}
    (hx : IsAnyActualCriticalStart x) :
    ∃! m : ℕ, IsActualCriticalStart m x := by
  rcases hx with ⟨m, hm⟩
  refine ⟨m, hm, ?_⟩
  intro n hn
  exact actualCriticalStart_width_unique hn hm

end Bridge
end Collatz3
