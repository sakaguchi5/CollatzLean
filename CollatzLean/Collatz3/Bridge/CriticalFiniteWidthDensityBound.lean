import CollatzLean.Collatz3.Bridge.CriticalFixedWidthDensity
import Mathlib.Algebra.BigOperators.Field

/-!
# Collatz3 Bridge: finite width family の density-sum bound

異なる critical width の actual start 集合は disjoint であり、
positive width の actual start はすべて奇数である。

そこで widths `1,...,L` を、最大 width `L` の共通 2-power block
`M_L` の中で同時に数える。各 smaller modulus `M_m` は `M_L` を割り、
幅 `m` の exact block count は `N_m * (M_L / M_m)` となる。

全 width の bounded start を odd residues へ単射することで、有限 cutoff ごとに

`sum_{1 ≤ m ≤ L} N_m / M_m ≤ 1/2`

を得る。これは無限和上界へ進む前の exact finite theorem である。
-/

namespace Collatz3
namespace Bridge

open scoped BigOperators

/-- Beatty index は単調。 -/
theorem beattyIndex_mono : Monotone Critical.beattyIndex :=
  monotone_nat_of_le_succ fun n =>
    Nat.le_of_lt (Critical.beattyIndex_lt_succ n)

/-- critical total depth も幅に関して単調。 -/
theorem criticalTwoDepth_mono : Monotone Critical.criticalTwoDepth := by
  intro m n hmn
  unfold Critical.criticalTwoDepth
  exact Nat.add_le_add_right (beattyIndex_mono hmn) 1

/-- `M_L / M_m` に対応する exact 2-power scale。 -/
def criticalStartScale (m L : ℕ) : ℕ :=
  2 ^ (Critical.criticalTwoDepth L - Critical.criticalTwoDepth m)

@[simp] theorem criticalStartScale_pos (m L : ℕ) :
    0 < criticalStartScale m L := by
  unfold criticalStartScale
  exact Arithmetic.twoPow_pos _

/-- `m ≤ L` なら `M_L = M_m * scale(m,L)`。 -/
theorem criticalStartModulus_mul_scale
    {m L : ℕ}
    (hmL : m ≤ L) :
    criticalStartModulus m * criticalStartScale m L =
      criticalStartModulus L := by
  have hDepth :
      Critical.criticalTwoDepth m ≤ Critical.criticalTwoDepth L :=
    criticalTwoDepth_mono hmL
  unfold criticalStartModulus criticalStartScale
  rw [← pow_add]
  congr 1
  omega

/-- common block `M_L` 内の width `m` count。 -/
theorem actualCriticalStartCount_commonBlock
    {m L : ℕ}
    (hm : 0 < m)
    (hmL : m ≤ L) :
    actualCriticalStartCount m (criticalStartModulus L) =
      criticalPartitionCount m * criticalStartScale m L := by
  rw [← criticalStartModulus_mul_scale hmL]
  exact actualCriticalStartCount_block_eq hm (criticalStartScale m L)

/-- `B` 未満の奇数。 -/
abbrev OddBelow (B : ℕ) :=
  {x : ℕ // x < B ∧ Odd x}

/-- width `1,...,L` の bounded actual critical starts を disjoint union として持つ。 -/
abbrev PositiveWidthCriticalStartsBelow (L B : ℕ) :=
  Σ i : Fin L, ActualCriticalStartBelow (i.1 + 1) B

/-- width-tagged start から underlying odd integer を忘れる。 -/
def positiveWidthStartToOddBelow
    (L B : ℕ) :
    PositiveWidthCriticalStartsBelow L B → OddBelow B :=
  fun T =>
    ⟨T.2.1,
      T.2.2.1,
      isActualCriticalStart_odd_of_pos (Nat.succ_pos T.1.1) T.2.2.2⟩

/--
幅一意性により、width tag を忘れても単射。
-/
theorem positiveWidthStartToOddBelow_injective
    (L B : ℕ) :
    Function.Injective (positiveWidthStartToOddBelow L B) := by
  intro A B'
  rcases A with ⟨i, x⟩
  rcases B' with ⟨j, y⟩
  intro h
  have hxy : x.1 = y.1 := congrArg Subtype.val h
  have hyAtX : IsActualCriticalStart (j.1 + 1) x.1 := by
    rw [hxy]
    exact y.2.2
  have hWidth : i.1 + 1 = j.1 + 1 :=
    actualCriticalStart_width_unique x.2.2 hyAtX
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  have hSub : x = y := by
    apply Subtype.ext
    exact hxy
  subst y
  rfl

/-- `M_m` の odd residue 数、すなわち `M_m / 2`。 -/
def criticalOddResidueCount (m : ℕ) : ℕ :=
  2 ^ Critical.criticalTwoDepth m

@[simp] theorem criticalOddResidueCount_pos (m : ℕ) :
    0 < criticalOddResidueCount m := by
  unfold criticalOddResidueCount
  exact Arithmetic.twoPow_pos _

/-- `M_m = 2 * criticalOddResidueCount m`。 -/
theorem criticalStartModulus_eq_two_mul_oddResidueCount
    (m : ℕ) :
    criticalStartModulus m = 2 * criticalOddResidueCount m := by
  unfold criticalStartModulus criticalOddResidueCount
  rw [pow_succ]
  ring

/--
`M_m` 未満の奇数は `Fin (M_m/2)` と exact に同値。
-/
noncomputable def finOddEquivOddBelowCriticalModulus
    (m : ℕ) :
    Fin (criticalOddResidueCount m) ≃
      OddBelow (criticalStartModulus m) where
  toFun k := by
    refine ⟨2 * k.1 + 1, ?_, ?_⟩
    · rw [criticalStartModulus_eq_two_mul_oddResidueCount]
      omega
    · exact ⟨k.1, rfl⟩
  invFun x := by
    let k := Classical.choose x.2.2
    have hkEq : x.1 = 2 * k + 1 :=
      Classical.choose_spec x.2.2
    refine ⟨k, ?_⟩
    have hxBound :
        x.1 < criticalStartModulus m :=
      x.2.1
    have hxBound' :
        x.1 < 2 * criticalOddResidueCount m := by
      calc
        x.1 < criticalStartModulus m := hxBound
        _ = 2 * criticalOddResidueCount m :=
          criticalStartModulus_eq_two_mul_oddResidueCount m
    omega
  left_inv k := by
    apply Fin.ext
    let x : OddBelow (criticalStartModulus m) :=
      ⟨2 * k.1 + 1,
        by
          rw [criticalStartModulus_eq_two_mul_oddResidueCount]
          omega,
        ⟨k.1, rfl⟩⟩
    let j := Classical.choose x.2.2
    have hj : x.1 = 2 * j + 1 := Classical.choose_spec x.2.2
    change j = k.1
    dsimp [x] at hj
    omega
  right_inv x := by
    apply Subtype.ext
    let k := Classical.choose x.2.2
    have hk : x.1 = 2 * k + 1 := Classical.choose_spec x.2.2
    exact hk.symm

/-- common critical block 内の odd integers の個数は exactly `M_L/2`。 -/
theorem oddBelow_criticalStartModulus_card
    (L : ℕ) :
    Nat.card (OddBelow (criticalStartModulus L)) =
      criticalOddResidueCount L := by
  calc
    Nat.card (OddBelow (criticalStartModulus L))
        = Nat.card (Fin (criticalOddResidueCount L)) :=
      (Nat.card_congr (finOddEquivOddBelowCriticalModulus L)).symm
    _ = criticalOddResidueCount L := Nat.card_fin _

/-- width-tagged bounded starts の cardinal は各 width count の和。 -/
theorem positiveWidthCriticalStartsBelow_card
    (L B : ℕ) :
    Nat.card (PositiveWidthCriticalStartsBelow L B) =
      ∑ i : Fin L, actualCriticalStartCount (i.1 + 1) B := by
  let : ∀ i : Fin L,
      Finite (ActualCriticalStartBelow (i.1 + 1) B) :=
    fun i => actualCriticalStartBelow_finite (i.1 + 1) B
  simpa [actualCriticalStartCount] using
    (Nat.card_sigma
      (α := Fin L)
      (β := fun i : Fin L => ActualCriticalStartBelow (i.1 + 1) B))

/--
共通 block `M_L` の中で widths `1,...,L` の start 総数は odd residue 数以下。
-/
theorem positiveWidths_commonBlock_count_le_odd
    (L : ℕ) :
    (∑ i : Fin L,
      actualCriticalStartCount (i.1 + 1) (criticalStartModulus L)) ≤
      criticalOddResidueCount L := by
  have hFinite : Finite (OddBelow (criticalStartModulus L)) := by
    exact
      Finite.of_injective
        (fun x : OddBelow (criticalStartModulus L) =>
          (⟨x.1, x.2.1⟩ : Fin (criticalStartModulus L)))
        (by
          intro a b h
          apply Subtype.ext
          exact congrArg Fin.val h)
  let : Finite (OddBelow (criticalStartModulus L)) := hFinite
  have hCard :
      Nat.card (PositiveWidthCriticalStartsBelow L (criticalStartModulus L)) ≤
        Nat.card (OddBelow (criticalStartModulus L)) :=
    Nat.card_le_card_of_injective
      (positiveWidthStartToOddBelow L (criticalStartModulus L))
      (positiveWidthStartToOddBelow_injective L (criticalStartModulus L))
  rw [positiveWidthCriticalStartsBelow_card, oddBelow_criticalStartModulus_card] at hCard
  exact hCard

/--
有限幅 `1,...,L` に対する pure integer density inequality。
各 width count を common modulus `M_L` へ持ち上げた exact 形。
-/
theorem finiteWidth_scaledPartitionCount_le_oddResidues
    (L : ℕ) :
    (∑ i : Fin L,
      criticalPartitionCount (i.1 + 1) *
        criticalStartScale (i.1 + 1) L) ≤
      criticalOddResidueCount L := by
  have h := positiveWidths_commonBlock_count_le_odd L
  apply le_trans ?_ h
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _hi
  have hiL : i.1 + 1 ≤ L := by
    exact Nat.succ_le_iff.mpr i.2
  exact (actualCriticalStartCount_commonBlock (Nat.succ_pos i.1) hiL).symm

/--
有限幅 density sum の実数版。

`sum_{m=1}^L N_m / M_m ≤ 1/2`。
-/
theorem finiteWidth_density_sum_le_half
    (L : ℕ) :
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (criticalStartModulus (i.1 + 1) : ℝ)) ≤
      (1 : ℝ) / 2 := by
  let ML := criticalStartModulus L
  let HL := criticalOddResidueCount L
  have hML : (0 : ℝ) < (ML : ℝ) := by
    exact_mod_cast criticalStartModulus_pos L
  have hNat := finiteWidth_scaledPartitionCount_le_oddResidues L
  have hCast :
      (∑ i : Fin L,
          ((criticalPartitionCount (i.1 + 1) *
            criticalStartScale (i.1 + 1) L : ℕ) : ℝ)) ≤
        (HL : ℝ) := by
    exact_mod_cast hNat
  have hTerm : ∀ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
          (criticalStartModulus (i.1 + 1) : ℝ) =
        ((criticalPartitionCount (i.1 + 1) *
            criticalStartScale (i.1 + 1) L : ℕ) : ℝ) /
          (ML : ℝ) := by
    intro i
    have hiL : i.1 + 1 ≤ L := Nat.succ_le_iff.mpr i.2
    have hFactor := criticalStartModulus_mul_scale hiL
    have hMi : 0 < criticalStartModulus (i.1 + 1) :=
      criticalStartModulus_pos _
    have hScale : 0 < criticalStartScale (i.1 + 1) L :=
      criticalStartScale_pos _ _
    have hMiR : (criticalStartModulus (i.1 + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hMi)
    have hScaleR : (criticalStartScale (i.1 + 1) L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hScale)
    have hFactorR :
        (ML : ℝ) =
          (criticalStartModulus (i.1 + 1) : ℝ) *
            (criticalStartScale (i.1 + 1) L : ℝ) := by
      dsimp [ML]
      exact_mod_cast hFactor.symm
    rw [hFactorR]
    push_cast
    field_simp [hMiR, hScaleR]
  calc
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (criticalStartModulus (i.1 + 1) : ℝ))
        =
        ∑ i : Fin L,
          (((criticalPartitionCount (i.1 + 1) *
            criticalStartScale (i.1 + 1) L : ℕ) : ℝ) /
            (ML : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hTerm i
    _ =
        (∑ i : Fin L,
          ((criticalPartitionCount (i.1 + 1) *
            criticalStartScale (i.1 + 1) L : ℕ) : ℝ)) /
          (ML : ℝ) := by
          rw [Finset.sum_div]
    _ ≤ (HL : ℝ) / (ML : ℝ) :=
      (div_le_div_iff_of_pos_right hML).2 hCast
    _ = (1 : ℝ) / 2 := by
      have hFactor : ML = 2 * HL := by
        dsimp [ML, HL]
        exact criticalStartModulus_eq_two_mul_oddResidueCount L
      have hHL : (HL : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (criticalOddResidueCount_pos L))
      rw [hFactor]
      push_cast
      field_simp [hHL]

end Bridge
end Collatz3
