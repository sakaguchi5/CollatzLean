import CollatzLean.Collatz3.Bridge.FullFirstCrossingDensity
import CollatzLean.Collatz3.Bridge.CriticalFiniteWidthDensityBound
import Mathlib.Algebra.BigOperators.Field

/-!
# Collatz3 Bridge: full first-crossing の finite-width density bound

full first-crossing でも異なる widths は同じ actual start を共有できない。
shorter width は terminal で `beattyIndex m + 1` 以上へ到達済みなのに、
longer width から見る同じ cut は proper prefix なので `beattyIndex m` 以下だからである。

widths `1,...,L` を共通 block `criticalStartModulus L = 2^(H_L+1)` で数え、
width-tagged full starts を odd integers へ単射する。

これにより

`sum_{m=1}^L N_m / 2^H_m ≤ 1/2`

を得る。従来の `M_m = 2^(H_m+1)` に戻せば requested bound

`sum_{m=1}^L N_m / M_m ≤ 1/4`

となる。
-/

namespace Collatz3
namespace Bridge

open scoped BigOperators

/-- 幅 `m<n` の full first-crossing actual runs は同じ start を共有できない。 -/
theorem no_common_start_of_full_first_crossing_width_lt
    {m n x y z : ℕ}
    (hmn : m < n)
    (Wm : Critical.FullFirstCrossingWord m)
    (Wn : Critical.FullFirstCrossingWord n)
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
            = Word.prefixTwoDepth (Wm.1 ++ t) m := by rw [hEq]
        _ = Word.prefixTwoDepth
              (Wm.1 ++ t) (Word.oddSteps Wm.1) := hIndex
        _ = Word.twoSteps Wm.1 := by
              unfold Word.prefixTwoDepth
              simp [Word.oddSteps, Word.twoSteps]
    have hRoof := Wn.2.prefixTwoDepth_le_beatty (k := m) hmn
    have hTerminal := Wm.2.criticalTwoDepth_le_twoSteps
    rw [hPrefix] at hRoof
    unfold Critical.criticalTwoDepth at hTerminal
    omega
  · rcases hRight with ⟨t, hEq, _hSuffix⟩
    have hSteps := congrArg Word.oddSteps hEq
    rw [Wm.2.oddSteps_eq, Word.oddSteps_append, Wn.2.oddSteps_eq] at hSteps
    omega

/-- 同じ actual start を持つ二つの full first-crossing widths は一致。 -/
theorem fullFirstCrossing_width_eq_of_common_actual_start
    {m n x y z : ℕ}
    (Wm : Critical.FullFirstCrossingWord m)
    (Wn : Critical.FullFirstCrossingWord n)
    (hRunM : Runs Wm.1 x y)
    (hRunN : Runs Wn.1 x z) :
    m = n := by
  by_contra hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact no_common_start_of_full_first_crossing_width_lt
      hlt Wm Wn hRunM hRunN
  · exact no_common_start_of_full_first_crossing_width_lt
      hgt Wn Wm hRunN hRunM

/-- `IsFullActualCriticalStart` が同じ整数で成立する幅は一意。 -/
theorem fullActualCriticalStart_width_unique
    {m n x : ℕ}
    (hm : IsFullActualCriticalStart m x)
    (hn : IsFullActualCriticalStart n x) :
    m = n := by
  rcases hm with ⟨Wm, y, hRunM⟩
  rcases hn with ⟨Wn, z, hRunN⟩
  exact fullFirstCrossing_width_eq_of_common_actual_start
    Wm Wn hRunM hRunN

/-- positive width の full actual critical start は奇数。 -/
theorem isFullActualCriticalStart_odd_of_pos
    {m x : ℕ}
    (hm : 0 < m)
    (hStart : IsFullActualCriticalStart m x) :
    Odd x := by
  rcases hStart with ⟨W, y, hRun⟩
  exact hRun.start_odd_of_nonempty (Critical.FullFirstCrossingWord.nonempty hm W)

/-- full modulus `2^H_m` から common critical block `2^(H_L+1)` への scale。 -/
def fullToCriticalBlockScale (m L : ℕ) : ℕ :=
  2 ^ (Critical.criticalTwoDepth L + 1 - Critical.criticalTwoDepth m)

@[simp] theorem fullToCriticalBlockScale_pos (m L : ℕ) :
    0 < fullToCriticalBlockScale m L := by
  unfold fullToCriticalBlockScale
  exact Arithmetic.twoPow_pos _

/-- `m≤L` なら `fullModulus(m) * scale = criticalStartModulus(L)`。 -/
theorem fullCrossingStartModulus_mul_fullToCriticalBlockScale
    {m L : ℕ}
    (hmL : m ≤ L) :
    fullCrossingStartModulus m * fullToCriticalBlockScale m L =
      criticalStartModulus L := by
  have hDepth :
      Critical.criticalTwoDepth m ≤ Critical.criticalTwoDepth L :=
    criticalTwoDepth_mono hmL
  unfold fullCrossingStartModulus Arithmetic.twoPowModulus
    fullToCriticalBlockScale criticalStartModulus
  rw [← pow_add]
  congr 1
  omega

/-- common block 内の fixed-width full-start count。 -/
theorem fullActualCriticalStartCount_commonCriticalBlock
    {m L : ℕ}
    (hm : 0 < m)
    (hmL : m ≤ L) :
    fullActualCriticalStartCount m (criticalStartModulus L) =
      criticalPartitionCount m * fullToCriticalBlockScale m L := by
  rw [← fullCrossingStartModulus_mul_fullToCriticalBlockScale hmL]
  exact fullActualCriticalStartCount_block_eq hm (fullToCriticalBlockScale m L)

/-- widths `1,...,L` の full starts を width-tagged disjoint union として持つ。 -/
abbrev PositiveWidthFullCriticalStartsBelow (L B : ℕ) :=
  Σ i : Fin L, FullActualCriticalStartBelow (i.1 + 1) B

/-- width tag を忘れて underlying odd integer へ送る。 -/
def positiveWidthFullStartToOddBelow
    (L B : ℕ) :
    PositiveWidthFullCriticalStartsBelow L B → OddBelow B :=
  fun T =>
    ⟨T.2.1,
      T.2.2.1,
      isFullActualCriticalStart_odd_of_pos (Nat.succ_pos T.1.1) T.2.2.2⟩

/-- full width の一意性により width tag を忘れても単射。 -/
theorem positiveWidthFullStartToOddBelow_injective
    (L B : ℕ) :
    Function.Injective (positiveWidthFullStartToOddBelow L B) := by
  intro A B'
  rcases A with ⟨i, x⟩
  rcases B' with ⟨j, y⟩
  intro h
  have hxy : x.1 = y.1 := congrArg Subtype.val h
  have hyAtX : IsFullActualCriticalStart (j.1 + 1) x.1 := by
    rw [hxy]
    exact y.2.2
  have hWidth : i.1 + 1 = j.1 + 1 :=
    fullActualCriticalStart_width_unique x.2.2 hyAtX
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  have hSub : x = y := by
    apply Subtype.ext
    exact hxy
  subst y
  rfl

/-- width-tagged bounded full starts の cardinal は各 width count の和。 -/
theorem positiveWidthFullCriticalStartsBelow_card
    (L B : ℕ) :
    Nat.card (PositiveWidthFullCriticalStartsBelow L B) =
      ∑ i : Fin L, fullActualCriticalStartCount (i.1 + 1) B := by
  let : ∀ i : Fin L,
      Finite (FullActualCriticalStartBelow (i.1 + 1) B) :=
    fun i => fullActualCriticalStartBelow_finite (i.1 + 1) B
  simpa [fullActualCriticalStartCount] using
    (Nat.card_sigma
      (α := Fin L)
      (β := fun i : Fin L => FullActualCriticalStartBelow (i.1 + 1) B))

/-- common critical block 内で widths `1,...,L` の full starts 総数は odd 数以下。 -/
theorem positiveFullWidths_commonCriticalBlock_count_le_odd
    (L : ℕ) :
    (∑ i : Fin L,
      fullActualCriticalStartCount (i.1 + 1) (criticalStartModulus L)) ≤
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
      Nat.card (PositiveWidthFullCriticalStartsBelow L (criticalStartModulus L)) ≤
        Nat.card (OddBelow (criticalStartModulus L)) :=
    Nat.card_le_card_of_injective
      (positiveWidthFullStartToOddBelow L (criticalStartModulus L))
      (positiveWidthFullStartToOddBelow_injective L (criticalStartModulus L))
  rw [positiveWidthFullCriticalStartsBelow_card,
      oddBelow_criticalStartModulus_card] at hCard
  exact hCard

/-- pure integer scaled inequality for full first-crossing widths `1,...,L`。 -/
theorem finiteWidth_fullScaledPartitionCount_le_oddResidues
    (L : ℕ) :
    (∑ i : Fin L,
      criticalPartitionCount (i.1 + 1) *
        fullToCriticalBlockScale (i.1 + 1) L) ≤
      criticalOddResidueCount L := by
  have h := positiveFullWidths_commonCriticalBlock_count_le_odd L
  apply le_trans ?_ h
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _hi
  have hiL : i.1 + 1 ≤ L := Nat.succ_le_iff.mpr i.2
  exact
    (fullActualCriticalStartCount_commonCriticalBlock
      (Nat.succ_pos i.1) hiL).symm

/-- full first-crossing density sum: `sum N_m / 2^H_m ≤ 1/2`。 -/
theorem finiteWidth_fullDensity_sum_le_half
    (L : ℕ) :
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (fullCrossingStartModulus (i.1 + 1) : ℝ)) ≤
      (1 : ℝ) / 2 := by
  let ML := criticalStartModulus L
  let HL := criticalOddResidueCount L
  have hML : (0 : ℝ) < (ML : ℝ) := by
    exact_mod_cast criticalStartModulus_pos L
  have hNat := finiteWidth_fullScaledPartitionCount_le_oddResidues L
  have hCast :
      (∑ i : Fin L,
          ((criticalPartitionCount (i.1 + 1) *
            fullToCriticalBlockScale (i.1 + 1) L : ℕ) : ℝ)) ≤
        (HL : ℝ) := by
    exact_mod_cast hNat
  have hTerm : ∀ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
          (fullCrossingStartModulus (i.1 + 1) : ℝ) =
        ((criticalPartitionCount (i.1 + 1) *
            fullToCriticalBlockScale (i.1 + 1) L : ℕ) : ℝ) /
          (ML : ℝ) := by
    intro i
    have hiL : i.1 + 1 ≤ L := Nat.succ_le_iff.mpr i.2
    have hFactor := fullCrossingStartModulus_mul_fullToCriticalBlockScale hiL
    have hMi : 0 < fullCrossingStartModulus (i.1 + 1) :=
      fullCrossingStartModulus_pos _
    have hScale : 0 < fullToCriticalBlockScale (i.1 + 1) L :=
      fullToCriticalBlockScale_pos _ _
    have hMiR : (fullCrossingStartModulus (i.1 + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hMi)
    have hScaleR : (fullToCriticalBlockScale (i.1 + 1) L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hScale)
    have hFactorR :
        (ML : ℝ) =
          (fullCrossingStartModulus (i.1 + 1) : ℝ) *
            (fullToCriticalBlockScale (i.1 + 1) L : ℝ) := by
      dsimp [ML]
      exact_mod_cast hFactor.symm
    rw [hFactorR]
    push_cast
    field_simp [hMiR, hScaleR]
  calc
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (fullCrossingStartModulus (i.1 + 1) : ℝ))
        =
        ∑ i : Fin L,
          (((criticalPartitionCount (i.1 + 1) *
            fullToCriticalBlockScale (i.1 + 1) L : ℕ) : ℝ) /
            (ML : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hTerm i
    _ =
        (∑ i : Fin L,
          ((criticalPartitionCount (i.1 + 1) *
            fullToCriticalBlockScale (i.1 + 1) L : ℕ) : ℝ)) /
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

/--
requested strengthened bound:

`sum_{m=1}^L N_m / M_m ≤ 1/4`,  `M_m = 2^(H_m+1)`。
-/
theorem finiteWidth_density_sum_le_quarter
    (L : ℕ) :
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (criticalStartModulus (i.1 + 1) : ℝ)) ≤
      (1 : ℝ) / 4 := by
  have hFull := finiteWidth_fullDensity_sum_le_half L
  have hTerm : ∀ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
          (criticalStartModulus (i.1 + 1) : ℝ) =
        ((criticalPartitionCount (i.1 + 1) : ℝ) /
          (fullCrossingStartModulus (i.1 + 1) : ℝ)) / 2 := by
    intro i
    have hF : (fullCrossingStartModulus (i.1 + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (fullCrossingStartModulus_pos (i.1 + 1))
    have hRel :=
      criticalStartModulus_eq_two_mul_fullCrossingStartModulus (i.1 + 1)
    have hRelR :
        (criticalStartModulus (i.1 + 1) : ℝ) =
          2 * (fullCrossingStartModulus (i.1 + 1) : ℝ) := by
      exact_mod_cast hRel
    rw [hRelR]
    field_simp [hF]
  calc
    (∑ i : Fin L,
      (criticalPartitionCount (i.1 + 1) : ℝ) /
        (criticalStartModulus (i.1 + 1) : ℝ))
        =
        ∑ i : Fin L,
          ((criticalPartitionCount (i.1 + 1) : ℝ) /
            (fullCrossingStartModulus (i.1 + 1) : ℝ)) / 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hTerm i
    _ =
        (∑ i : Fin L,
          (criticalPartitionCount (i.1 + 1) : ℝ) /
            (fullCrossingStartModulus (i.1 + 1) : ℝ)) / 2 := by
          rw [Finset.sum_div]
    _ ≤ ((1 : ℝ) / 2) / 2 :=
      (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hFull
    _ = (1 : ℝ) / 4 := by norm_num

end Bridge
end Collatz3
