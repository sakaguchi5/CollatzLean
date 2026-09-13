import CollatzLean.Collatz3.Bridge.CriticalWidthDisjoint
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: fixed-width critical start の exact counting

固定幅 `m > 0` では actual critical starts が

`R(P) + M_m k`

という `N_m` 本の pairwise disjoint arithmetic fiber に完全分類されている。
本ファイルではこの分類を有限区間 counting に移す。

特に full block `q * M_m` 未満では個数が exact に

`q * N_m`

となる。任意 cutoff `X` では floor block の間に挟むことで、
主項 `(N_m / M_m) X` から一周期分だけの discrepancy しか持たないことを示す。
-/

namespace Collatz3
namespace Bridge

/-- 幅 `m` の actual critical start のうち `B` 未満のもの。 -/
abbrev ActualCriticalStartBelow (m B : ℕ) :=
  {x : ℕ // x < B ∧ IsActualCriticalStart m x}

/-- bounded start type は有限。 -/
theorem actualCriticalStartBelow_finite
    (m B : ℕ) :
    Finite (ActualCriticalStartBelow m B) := by
  exact
    Finite.of_injective
      (fun x : ActualCriticalStartBelow m B =>
        (⟨x.1, x.2.1⟩ : Fin B))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Fin.val h)

/-- `B` 未満の幅 `m` actual critical start の個数。 -/
noncomputable def actualCriticalStartCount (m B : ℕ) : ℕ :=
  Nat.card (ActualCriticalStartBelow m B)

/-- cutoff を大きくすると bounded start type を包含できる。 -/
def actualCriticalStartBelowMap
    {m B C : ℕ}
    (hBC : B ≤ C) :
    ActualCriticalStartBelow m B → ActualCriticalStartBelow m C :=
  fun x => ⟨x.1, lt_of_lt_of_le x.2.1 hBC, x.2.2⟩

/-- cutoff inclusion は単射。 -/
theorem actualCriticalStartBelowMap_injective
    {m B C : ℕ}
    (hBC : B ≤ C) :
    Function.Injective
      (actualCriticalStartBelowMap (m := m) hBC) := by
  intro a b h
  apply Subtype.ext
  simpa [actualCriticalStartBelowMap] using
    congrArg
      (fun x : ActualCriticalStartBelow m C => x.1)
      h

/-- bounded count は cutoff に関して単調。 -/
theorem actualCriticalStartCount_mono
    {m B C : ℕ}
    (hBC : B ≤ C) :
    actualCriticalStartCount m B ≤ actualCriticalStartCount m C := by
  let : Finite (ActualCriticalStartBelow m C) :=
    actualCriticalStartBelow_finite m C
  exact
    Nat.card_le_card_of_injective
      (actualCriticalStartBelowMap (m := m) hBC)
      (actualCriticalStartBelowMap_injective (m := m) hBC)

/--
partition と `k < q` から、最初の `q` 周期内の actual critical start を作る。
-/
def criticalBlockCodeToStart
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    (RestrictedCriticalPartition m × Fin q) →
      ActualCriticalStartBelow m (criticalStartModulus m * q) :=
  fun code => by
    let P := code.1
    let k := code.2
    let W := criticalWordOfPartition m hm P
    refine ⟨liftedCriticalStart hm P k.1, ?_, ?_⟩
    · have hR :
          Word.canonicalStart W.1 < criticalStartModulus m :=
        canonicalStart_lt_criticalStartModulus W
      have hkSucc : k.1 + 1 ≤ q := Nat.succ_le_iff.mpr k.2
      unfold liftedCriticalStart
      change
        Word.canonicalStart W.1 + criticalStartModulus m * k.1 <
          criticalStartModulus m * q
      calc
        Word.canonicalStart W.1 + criticalStartModulus m * k.1
            < criticalStartModulus m + criticalStartModulus m * k.1 :=
          Nat.add_lt_add_right hR _
        _ = criticalStartModulus m * (k.1 + 1) := by ring
        _ ≤ criticalStartModulus m * q :=
          Nat.mul_le_mul_left _ hkSucc
    · exact
        (isActualCriticalStart_iff_exists_partition_lift hm).2
          ⟨P, k.1, rfl⟩

/-- block encoding は単射。 -/
theorem criticalBlockCodeToStart_injective
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    Function.Injective (criticalBlockCodeToStart hm q) := by
  intro a b h
  rcases a with ⟨P, k⟩
  rcases b with ⟨Q, l⟩
  have hStart :
      liftedCriticalStart hm P k.1 = liftedCriticalStart hm Q l.1 :=
    congrArg Subtype.val h
  have hPQ : P = Q :=
    liftedCriticalStart_eq_implies_partition_eq hm hStart
  subst Q
  apply Prod.ext
  · rfl
  · apply Fin.ext
    unfold liftedCriticalStart at hStart
    have hMul :
        criticalStartModulus m * k.1 =
          criticalStartModulus m * l.1 :=
      Nat.add_left_cancel hStart
    exact Nat.mul_left_cancel (criticalStartModulus_pos m) hMul

/-- block encoding は全射。 -/
theorem criticalBlockCodeToStart_surjective
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    Function.Surjective (criticalBlockCodeToStart hm q) := by
  intro x
  rcases
      (isActualCriticalStart_iff_exists_partition_lift hm).1 x.2.2
      with ⟨P, k, hx⟩
  have hk : k < q := by
    by_contra hNot
    have hqk : q ≤ k := Nat.le_of_not_gt hNot
    have hMul :
        criticalStartModulus m * q ≤ criticalStartModulus m * k :=
      Nat.mul_le_mul_left _ hqk
    have hTail :
        criticalStartModulus m * k ≤ liftedCriticalStart hm P k := by
      unfold liftedCriticalStart
      omega
    have hBound : criticalStartModulus m * q ≤ x.1 := by
      rw [hx]
      exact le_trans hMul hTail
    omega
  refine ⟨(P, ⟨k, hk⟩), ?_⟩
  apply Subtype.ext
  exact hx.symm

/--
最初の `q` 個の modulus block と `partition × Fin q` は exact に同値。
-/
noncomputable def criticalBlockCodeEquivStartBelow
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    (RestrictedCriticalPartition m × Fin q) ≃
      ActualCriticalStartBelow m (criticalStartModulus m * q) :=
  Equiv.ofBijective
    (criticalBlockCodeToStart hm q)
    ⟨criticalBlockCodeToStart_injective hm q,
      criticalBlockCodeToStart_surjective hm q⟩

/--
full `q` blocks では bounded start count は exact に `N_m * q`。
-/
theorem actualCriticalStartCount_block_eq
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    actualCriticalStartCount m (criticalStartModulus m * q) =
      criticalPartitionCount m * q := by
  unfold actualCriticalStartCount
  calc
    Nat.card
        (ActualCriticalStartBelow m (criticalStartModulus m * q))
        = Nat.card (RestrictedCriticalPartition m × Fin q) :=
      (Nat.card_congr (criticalBlockCodeEquivStartBelow hm q)).symm
    _ = Nat.card (RestrictedCriticalPartition m) * Nat.card (Fin q) :=
      Nat.card_prod _ _
    _ = criticalPartitionCount m * q := by
      simp [criticalPartitionCount]

/-- floor block は cutoff 以下。 -/
theorem criticalStartModulus_mul_div_le
    (m X : ℕ) :
    criticalStartModulus m * (X / criticalStartModulus m) ≤ X := by
  have h := Nat.mod_add_div X (criticalStartModulus m)
  omega

/-- cutoff は次の modulus block より小さい。 -/
theorem lt_criticalStartModulus_mul_div_add_one
    (m X : ℕ) :
    X < criticalStartModulus m * (X / criticalStartModulus m + 1) := by
  let M := criticalStartModulus m
  have hM : 0 < M := criticalStartModulus_pos m
  have hmod : X % M < M := Nat.mod_lt X hM
  have hdiv : X % M + M * (X / M) = X := Nat.mod_add_div X M
  calc
    X = X % M + M * (X / M) := hdiv.symm
    _ < M + M * (X / M) := Nat.add_lt_add_right hmod _
    _ = M * (X / M + 1) := by ring

/--
任意 cutoff `X` の count は、直前と直後の full block count の間にある。
-/
theorem actualCriticalStartCount_sandwich
    {m X : ℕ}
    (hm : 0 < m) :
    criticalPartitionCount m * (X / criticalStartModulus m) ≤
        actualCriticalStartCount m X ∧
      actualCriticalStartCount m X ≤
        criticalPartitionCount m * (X / criticalStartModulus m + 1) := by
  let q := X / criticalStartModulus m
  constructor
  · calc
      criticalPartitionCount m * q
          = actualCriticalStartCount m (criticalStartModulus m * q) :=
        (actualCriticalStartCount_block_eq hm q).symm
      _ ≤ actualCriticalStartCount m X :=
        actualCriticalStartCount_mono
          (criticalStartModulus_mul_div_le m X)
  · calc
      actualCriticalStartCount m X
          ≤ actualCriticalStartCount m (criticalStartModulus m * (q + 1)) :=
        actualCriticalStartCount_mono
          (le_of_lt (lt_criticalStartModulus_mul_div_add_one m X))
      _ = criticalPartitionCount m * (q + 1) :=
        actualCriticalStartCount_block_eq hm (q + 1)

/--
主項 `N_m X / M_m` に対する cross-multiplied discrepancy。
一周期分 `M_m N_m` を越えない。
-/
theorem actualCriticalStartCount_cross_discrepancy
    {m X : ℕ}
    (hm : 0 < m) :
    criticalStartModulus m * actualCriticalStartCount m X ≤
        criticalPartitionCount m * X +
          criticalStartModulus m * criticalPartitionCount m ∧
      criticalPartitionCount m * X ≤
        criticalStartModulus m * actualCriticalStartCount m X +
          criticalStartModulus m * criticalPartitionCount m := by
  let M := criticalStartModulus m
  let N := criticalPartitionCount m
  let C := actualCriticalStartCount m X
  let q := X / M
  have hSand := actualCriticalStartCount_sandwich (m := m) (X := X) hm
  have hLower : N * q ≤ C := by simpa [M, N, C, q] using hSand.1
  have hUpper : C ≤ N * (q + 1) := by simpa [M, N, C, q] using hSand.2
  have hBlockLower : M * q ≤ X := by
    simpa [M, q] using criticalStartModulus_mul_div_le m X
  have hBlockUpper : X ≤ M * (q + 1) := by
    exact le_of_lt (by simpa [M, q] using lt_criticalStartModulus_mul_div_add_one m X)
  constructor
  · calc
      M * C ≤ M * (N * (q + 1)) := Nat.mul_le_mul_left M hUpper
      _ = N * (M * q) + M * N := by ring
      _ ≤ N * X + M * N :=
        Nat.add_le_add_right (Nat.mul_le_mul_left N hBlockLower) _
  · calc
      N * X ≤ N * (M * (q + 1)) := Nat.mul_le_mul_left N hBlockUpper
      _ = M * (N * q) + M * N := by ring
      _ ≤ M * C + M * N :=
        Nat.add_le_add_right (Nat.mul_le_mul_left M hLower) _

end Bridge
end Collatz3
