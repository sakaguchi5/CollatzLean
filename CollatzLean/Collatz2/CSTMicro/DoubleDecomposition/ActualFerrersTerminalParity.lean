import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualFerrersSuffixThreeAdicCorridor

/-!
# actual Ferrers terminal positive defect and parity

actual critical-defect profile の最後の正 column を canonical に取り出し、
whole Ferrers deficit の exact 3-adic order と terminal defect の parity を結ぶ。

中心結果は

  terminal defect odd
    <->
  criticalization start `p-v` = terminal positive endpoint `t+1`.

従って odd branch は Hensel corridor の nonempty positive part を持たない `d=0` branch、
even branch は `p-v < t+1` となる genuine suffix-Hensel branch である。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open ExternalArithmetic

/-- actual word 内で critical defect が正の cut の有限集合。 -/
def positiveCriticalDefectSet
    (w : Word) : Finset ℕ :=
  (Finset.range (Word.oddSteps w)).filter
    (fun k => 0 < Word.criticalDefect w k)

@[simp] theorem mem_positiveCriticalDefectSet_iff
    (w : Word)
    {k : ℕ} :
    k ∈ positiveCriticalDefectSet w ↔
      k < Word.oddSteps w ∧ 0 < Word.criticalDefect w k := by
  simp [positiveCriticalDefectSet]

/-- terminal positive defect を、右側がすべて zero であることまで含めて束ねる。 -/
structure TerminalPositiveDefectData (w : Word) where
  index : ℕ
  index_lt : index < Word.oddSteps w
  positive : 0 < Word.criticalDefect w index
  zero_after :
    ∀ k : ℕ,
      index < k →
      k < Word.oddSteps w →
      Word.criticalDefect w k = 0

/-- positive defect set の最大要素から canonical terminal data を作る。 -/
noncomputable def terminalPositiveDefectDataOfNonempty
    (w : Word)
    (hNE : (positiveCriticalDefectSet w).Nonempty) :
    TerminalPositiveDefectData w := by
  classical
  let t := (positiveCriticalDefectSet w).max' hNE
  have htMem : t ∈ positiveCriticalDefectSet w := by
    dsimp [t]
    exact Finset.max'_mem _ _
  have htSpec := (mem_positiveCriticalDefectSet_iff w).1 htMem
  refine {
    index := t
    index_lt := htSpec.1
    positive := htSpec.2
    zero_after := ?_
  }
  intro k htk hkp
  by_contra hne
  have hkPos : 0 < Word.criticalDefect w k := Nat.pos_of_ne_zero hne
  have hkMem : k ∈ positiveCriticalDefectSet w :=
    (mem_positiveCriticalDefectSet_iff w).2 ⟨hkp, hkPos⟩
  have hle : k ≤ t := by
    dsimp [t]
    exact Finset.le_max' _ _ hkMem
  omega

/-- exact 3-adic order を持つ整数は zero ではない。 -/
theorem exactThreeAdicOrder_ne_zero
    {z : ℤ}
    {v : ℕ}
    (h : ExactThreeAdicOrder z v) :
    z ≠ 0 := by
  intro hz
  apply h.2
  rw [hz]
  simp

/-- 指定区間で defect が全て zero なら Ferrers interval deficit も zero。 -/
theorem actualFerrersSegmentDeficitZ_eq_zero_of_defect_zero
    (w : Word)
    (start n : ℕ)
    (hZero :
      ∀ j : ℕ,
        j < n →
        Word.criticalDefect w (start + j) = 0) :
    actualFerrersSegmentDeficitZ w start n = 0 := by
  induction n with
  | zero =>
      simp [actualFerrersSegmentDeficitZ, actualFerrersBandsSegment,
        integerFerrersDeficit]
  | succ n ih =>
      have hPrev :
          ∀ j : ℕ,
            j < n →
            Word.criticalDefect w (start + j) = 0 := by
        intro j hj
        exact hZero j (by omega)
      have hLast : Word.criticalDefect w (start + n) = 0 :=
        hZero n (by omega)
      have hColumn : actualFerrersColumnDeficitZ w (start + n) = 0 := by
        unfold actualFerrersColumnDeficitZ
        rw [hLast]
        simp [criticalDefectColumnBands, integerFerrersDeficit]
      rw [actualFerrersSegmentDeficitZ_succ_right, ih hPrev, hColumn]
      simp

/-- whole actual deficit が nonzero なら positive defect column は存在する。 -/
theorem positiveCriticalDefectSet_nonempty_of_suffix_ne_zero
    (w : Word)
    (hNe : actualFerrersSuffixZ w 0 ≠ 0) :
    (positiveCriticalDefectSet w).Nonempty := by
  by_contra hNone
  have hZero :
      ∀ k : ℕ,
        k < Word.oddSteps w →
        Word.criticalDefect w k = 0 := by
    intro k hk
    by_contra hne
    have hkPos : 0 < Word.criticalDefect w k := Nat.pos_of_ne_zero hne
    apply hNone
    exact ⟨k, (mem_positiveCriticalDefectSet_iff w).2 ⟨hk, hkPos⟩⟩
  have hAllZero :=
    actualFerrersSegmentDeficitZ_eq_zero_of_defect_zero
      w 0 (Word.oddSteps w) (by
        intro j hj
        simpa using hZero j hj)
  apply hNe
  simpa [actualFerrersSuffixZ] using hAllZero

/-- exact-order actual deficit から canonical terminal positive defect を取る。 -/
noncomputable def terminalPositiveDefectDataOfExactOrder
    (w : Word)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v) :
    TerminalPositiveDefectData w :=
  terminalPositiveDefectDataOfNonempty w
    (positiveCriticalDefectSet_nonempty_of_suffix_ne_zero
      w (exactThreeAdicOrder_ne_zero hOrder))

/-- terminal positive endpoint `c=t+1` より右の suffix deficit は zero。 -/
theorem actualFerrersSuffixZ_terminalPositiveEndpoint_eq_zero
    {w : Word}
    (T : TerminalPositiveDefectData w) :
    actualFerrersSuffixZ w (T.index + 1) = 0 := by
  unfold actualFerrersSuffixZ
  apply actualFerrersSegmentDeficitZ_eq_zero_of_defect_zero
  intro j hj
  apply T.zero_after
  · omega
  · omega

/-- terminal positive cut の suffix はその一列 deficit だけ。 -/
theorem actualFerrersSuffixZ_terminalPositive_eq_column
    {w : Word}
    (T : TerminalPositiveDefectData w) :
    actualFerrersSuffixZ w T.index =
      actualFerrersColumnDeficitZ w T.index := by
  have hStep := actualFerrersSuffixZ_step w T.index_lt
  rw [actualFerrersSuffixZ_terminalPositiveEndpoint_eq_zero T] at hStep
  simpa using hStep

/-- `3^r | 3^R` for `r <= R`。 -/
private theorem threePow_dvd_threePow_of_le
    {r R : ℕ}
    (h : r ≤ R) :
    (3 : ℤ) ^ r ∣ (3 : ℤ) ^ R := by
  refine ⟨(3 : ℤ) ^ (R - r), ?_⟩
  have hExp : R = r + (R - r) := by omega
  rw [hExp, pow_add]
  simp only [add_tsub_cancel_left]


/-- `3 | 4^k - 1`。 -/
private theorem three_dvd_fourPow_sub_one
    (k : ℕ) :
    (3 : ℤ) ∣ (4 : ℤ) ^ k - 1 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rcases ih with ⟨z, hz⟩
      refine ⟨4 * z + 1, ?_⟩
      rw [pow_succ]
      calc
        (4 : ℤ) ^ k * 4 - 1 =
            4 * ((4 : ℤ) ^ k - 1) + 3 := by
          ring
        _ = 4 * (3 * z) + 3 := by
          rw [hz]
        _ = 3 * (4 * z + 1) := by
          ring

/-- even exponent なら `3 | 2^n - 1`。 -/
private theorem three_dvd_twoPow_sub_one_of_even
    {n : ℕ}
    (hEven : n % 2 = 0) :
    (3 : ℤ) ∣ (2 : ℤ) ^ n - 1 := by
  let k := n / 2
  have hDecomp := Nat.mod_add_div n 2
  have hn : n = 2 * k := by
    dsimp [k]
    omega
  have hPow : (2 : ℤ) ^ n = (4 : ℤ) ^ k := by
    rw [hn, pow_mul]
    norm_num
  rw [hPow]
  exact three_dvd_fourPow_sub_one k

/-- odd exponent なら `3` は `2^n - 1` を割らない。 -/
private theorem three_not_dvd_twoPow_sub_one_of_odd
    {n : ℕ}
    (hOdd : n % 2 = 1) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ n - 1 := by
  let k := n / 2
  have hDecomp := Nat.mod_add_div n 2
  have hn : n = 2 * k + 1 := by
    dsimp [k]
    omega
  have hPow : (2 : ℤ) ^ n = 2 * (4 : ℤ) ^ k := by
    rw [hn, pow_succ, pow_mul]
    norm_num
    ring
  intro hDiv
  rw [hPow] at hDiv
  have hBase := three_dvd_fourPow_sub_one k
  rcases hDiv with ⟨a, ha⟩
  rcases hBase with ⟨b, hb⟩
  have hOne : (3 : ℤ) ∣ 1 := by
    refine ⟨a - 2 * b, ?_⟩
    linarith
  norm_num at hOne

/-- exact 3-adic order は一意。 -/
private theorem exactThreeAdicOrder_unique
    {z : ℤ}
    {a b : ℕ}
    (ha : ExactThreeAdicOrder z a)
    (hb : ExactThreeAdicOrder z b) :
    a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hPow : (3 : ℤ) ^ (a + 1) ∣ (3 : ℤ) ^ b :=
      threePow_dvd_threePow_of_le (by omega)
    exact ha.2 (dvd_trans hPow hb.1)
  · have hPow : (3 : ℤ) ^ (b + 1) ∣ (3 : ℤ) ^ a :=
      threePow_dvd_threePow_of_le (by omega)
    exact hb.2 (dvd_trans hPow ha.1)

/--
terminal positive defect が odd なら whole actual deficit の exact 3-adic order は
right zero-tail length `p-(t+1)` そのもの。
-/
theorem actualFerrersSuffix_exactThreeAdicOrder_of_terminalDefect_odd
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (T : TerminalPositiveDefectData w)
    (hOdd : Word.criticalDefect w T.index % 2 = 1) :
    ExactThreeAdicOrder
      (actualFerrersSuffixZ w 0)
      (Word.oddSteps w - (T.index + 1)) := by
  let r := Word.oddSteps w - (T.index + 1)
  change ExactThreeAdicOrder (actualFerrersSuffixZ w 0) r
  have hIndexLe : T.index ≤ Word.oddSteps w := Nat.le_of_lt T.index_lt
  have hSplit := actualFerrersSuffixZ_zero_split w hIndexLe
  have hPrefix := actualFerrersPrefixSegment_threePow_dvd C hIndexLe
  have hIndexSuccLe :
      T.index + 1 ≤ Word.oddSteps w := by
    exact Nat.succ_le_iff.mpr T.index_lt
  have hExp : Word.oddSteps w - T.index = r + 1 := by
    dsimp [r]
    omega
  rw [hExp] at hPrefix
  have hTerminal := actualFerrersSuffixZ_terminalPositive_eq_column T
  have hColumn := actualFerrersColumnDeficitZ_eq_factor C.2 T.index_lt
  have hColumnR :
      actualFerrersColumnDeficitZ w T.index =
        (2 : ℤ) ^ Word.prefixTwoDepth w T.index *
          ((2 : ℤ) ^ Word.criticalDefect w T.index - 1) *
          (3 : ℤ) ^ r := by
    simpa [r] using hColumn
  constructor
  · have hPrefixR : (3 : ℤ) ^ r ∣
        actualFerrersSegmentDeficitZ w 0 T.index := by
      exact dvd_trans
        (threePow_dvd_threePow_of_le (by omega : r ≤ r + 1)) hPrefix
    have hColumnDiv : (3 : ℤ) ^ r ∣
        actualFerrersColumnDeficitZ w T.index := by
      rw [hColumnR]
      refine ⟨
        (2 : ℤ) ^ Word.prefixTwoDepth w T.index *
          ((2 : ℤ) ^ Word.criticalDefect w T.index - 1), ?_⟩
      ring
    rw [hTerminal] at hSplit
    rw [hSplit]
    exact dvd_add hPrefixR hColumnDiv
  · intro hTooDeep
    have hColumnDeep : (3 : ℤ) ^ (r + 1) ∣
        actualFerrersColumnDeficitZ w T.index := by
      rw [hTerminal] at hSplit
      have hWholeMinusPrefix :
          actualFerrersColumnDeficitZ w T.index =
            actualFerrersSuffixZ w 0 -
              actualFerrersSegmentDeficitZ w 0 T.index := by
        linarith
      rw [hWholeMinusPrefix]
      exact dvd_sub hTooDeep hPrefix
    rcases hColumnDeep with ⟨z, hz⟩
    have hCommonNe : (3 : ℤ) ^ r ≠ 0 := by positivity
    have hFactored :
        (3 : ℤ) ^ r *
            ((2 : ℤ) ^ Word.prefixTwoDepth w T.index *
              ((2 : ℤ) ^ Word.criticalDefect w T.index - 1)) =
          (3 : ℤ) ^ r * (3 * z) := by
      calc
        (3 : ℤ) ^ r *
              ((2 : ℤ) ^ Word.prefixTwoDepth w T.index *
                ((2 : ℤ) ^ Word.criticalDefect w T.index - 1))
            = actualFerrersColumnDeficitZ w T.index := by
                rw [hColumnR]
                ring
        _ = (3 : ℤ) ^ (r + 1) * z := hz
        _ = (3 : ℤ) ^ r * (3 * z) := by
              rw [pow_succ]
              ring
    have hCancel :
        (2 : ℤ) ^ Word.prefixTwoDepth w T.index *
            ((2 : ℤ) ^ Word.criticalDefect w T.index - 1) =
          3 * z :=
      mul_left_cancel₀ hCommonNe hFactored
    have hThreeMul :
        (3 : ℤ) ∣
          (2 : ℤ) ^ Word.prefixTwoDepth w T.index *
            ((2 : ℤ) ^ Word.criticalDefect w T.index - 1) := by
      exact ⟨z, hCancel⟩
    have hThreeForce :
        (3 : ℤ) ∣
          ((2 : ℤ) ^ Word.criticalDefect w T.index - 1) := by
      have h := MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow
        (e := 1)
        (a := Word.prefixTwoDepth w T.index)
        (z := ((2 : ℤ) ^ Word.criticalDefect w T.index - 1))
        (by simpa using hThreeMul)
      simpa using h
    exact three_not_dvd_twoPow_sub_one_of_odd hOdd hThreeForce

/--
terminal positive defect が even なら whole deficit は terminal zero-tail より
さらに一段深い 3-power を持つ。
-/
theorem actualFerrersSuffix_threePow_succ_dvd_of_terminalDefect_even
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (T : TerminalPositiveDefectData w)
    (hEven : Word.criticalDefect w T.index % 2 = 0) :
    (3 : ℤ) ^ (Word.oddSteps w - (T.index + 1) + 1) ∣
      actualFerrersSuffixZ w 0 := by
  let r := Word.oddSteps w - (T.index + 1)
  change (3 : ℤ) ^ (r + 1) ∣ actualFerrersSuffixZ w 0
  have hIndexLe : T.index ≤ Word.oddSteps w := Nat.le_of_lt T.index_lt
  have hSplit := actualFerrersSuffixZ_zero_split w hIndexLe
  have hPrefix := actualFerrersPrefixSegment_threePow_dvd C hIndexLe
  have hIndexSuccLe :
      T.index + 1 ≤ Word.oddSteps w := by
    exact Nat.succ_le_iff.mpr T.index_lt
  have hExp : Word.oddSteps w - T.index = r + 1 := by
    dsimp [r]
    omega
  rw [hExp] at hPrefix
  have hTerminal := actualFerrersSuffixZ_terminalPositive_eq_column T
  have hColumn := actualFerrersColumnDeficitZ_eq_factor C.2 T.index_lt
  have hColumnR :
      actualFerrersColumnDeficitZ w T.index =
        (2 : ℤ) ^ Word.prefixTwoDepth w T.index *
          ((2 : ℤ) ^ Word.criticalDefect w T.index - 1) *
          (3 : ℤ) ^ r := by
    simpa [r] using hColumn
  have hForce := three_dvd_twoPow_sub_one_of_even hEven
  rcases hForce with ⟨u, hu⟩
  have hColumnDeep : (3 : ℤ) ^ (r + 1) ∣
      actualFerrersColumnDeficitZ w T.index := by
    refine ⟨(2 : ℤ) ^ Word.prefixTwoDepth w T.index * u, ?_⟩
    rw [hColumnR, hu, pow_succ]
    ring
  rw [hTerminal] at hSplit
  rw [hSplit]
  exact dvd_add hPrefix hColumnDeep

/--
terminal positive defect が even なら criticalization start は terminal positive endpoint より
strict に左へ入る。これが `d>0` branch。
-/
theorem terminalDefect_even_implies_criticalization_lt_endpoint
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (T : TerminalPositiveDefectData w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    (hEven : Word.criticalDefect w T.index % 2 = 0) :
    Word.oddSteps w - v < T.index + 1 := by
  let r := Word.oddSteps w - (T.index + 1)
  have hDeep :=
    actualFerrersSuffix_threePow_succ_dvd_of_terminalDefect_even C T hEven
  change (3 : ℤ) ^ (r + 1) ∣ actualFerrersSuffixZ w 0 at hDeep
  have hRV : r + 1 ≤ v := by
    by_contra hnot
    have hvLt : v < r + 1 := by omega
    have hPow : (3 : ℤ) ^ (v + 1) ∣ (3 : ℤ) ^ (r + 1) :=
      threePow_dvd_threePow_of_le (by omega)
    exact hOrder.2 (dvd_trans hPow hDeep)
  dsimp [r] at hRV
  omega

/--
中心 lemma 3。

`v` を whole actual Ferrers deficit の exact 3-adic order、`t` を最後の正 defect とする。
このとき terminal defect が odd であることと

  p - v = t + 1

は同値。
-/
theorem terminalDefect_odd_iff_criticalization_eq_endpoint
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (T : TerminalPositiveDefectData w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w) :
    Word.criticalDefect w T.index % 2 = 1 ↔
      Word.oddSteps w - v = T.index + 1 := by
  constructor
  · intro hOdd
    have hTerminalOrder :=
      actualFerrersSuffix_exactThreeAdicOrder_of_terminalDefect_odd
        C T hOdd
    have hvEq :
        v = Word.oddSteps w - (T.index + 1) :=
      exactThreeAdicOrder_unique hOrder hTerminalOrder
    have hIndexSuccLe :
        T.index + 1 ≤ Word.oddSteps w :=
      Nat.succ_le_iff.mpr T.index_lt
    rw [hvEq]
    omega
  · intro hStartEq
    have hModLt : Word.criticalDefect w T.index % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    by_cases hOdd : Word.criticalDefect w T.index % 2 = 1
    · exact hOdd
    · have hEven : Word.criticalDefect w T.index % 2 = 0 := by omega
      have hDeep :=
        actualFerrersSuffix_threePow_succ_dvd_of_terminalDefect_even C T hEven
      have hvEq : v = Word.oddSteps w - (T.index + 1) := by omega
      rw [← hvEq] at hDeep
      exact (hOrder.2 hDeep).elim

end DoubleDecomposition
end CSTMicro
end Collatz2
