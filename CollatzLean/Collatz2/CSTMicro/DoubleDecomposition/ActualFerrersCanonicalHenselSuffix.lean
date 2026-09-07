import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualFerrersTerminalParity
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselChain

/-!
# actual Ferrers suffix -> canonical staircase Hensel chain

`d>0` (terminal defect even) branch で、actual critical-defect profile 自身から
canonical straight suffix を切り出し、`FreeBaseMonotoneHenselChain` を構成する。

PureB / Attached packet は仮定しない。

straight suffix の start は、criticalization start `s` から terminal positive cut `t`
までにある

* zero defect cut,
* unit prefix step でない cut

の最後のものの直後とする。bad cut が無ければ `s` 自身を start とする。
従って start 以後は defect が正で、terminal 一歩前まで actual prefix depth が exact `+1`。

normalized suffix quotient は前ファイルの
`ActualFerrersIntegralCorridor` をそのまま使う。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open ExternalArithmetic

/--
`[s,t]` 内で straight positive suffix を壊す cut。
`t` 自身では transition 条件を見ない。
-/
def actualStraightSuffixBadSet
    (w : Word)
    (s t : ℕ) : Finset ℕ :=
  (Finset.range (t + 1)).filter
    (fun k =>
      s ≤ k ∧
        (Word.criticalDefect w k = 0 ∨
          (k < t ∧
            Word.prefixTwoDepth w (k + 1) ≠
              Word.prefixTwoDepth w k + 1)))

@[simp] theorem mem_actualStraightSuffixBadSet_iff
    (w : Word)
    (s t k : ℕ) :
    k ∈ actualStraightSuffixBadSet w s t ↔
      k < t + 1 ∧
        s ≤ k ∧
        (Word.criticalDefect w k = 0 ∨
          (k < t ∧
            Word.prefixTwoDepth w (k + 1) ≠
              Word.prefixTwoDepth w k + 1)) := by
  simp [actualStraightSuffixBadSet]

/-- bad cut の最後の直後。bad cut が無ければ `s`。 -/
noncomputable def canonicalActualStraightSuffixStart
    (w : Word)
    (s t : ℕ) : ℕ := by
  classical
  exact if hNE : (actualStraightSuffixBadSet w s t).Nonempty then
    (actualStraightSuffixBadSet w s t).max' hNE + 1
  else
    s

/-- terminal defect が正なら canonical start は `[s,t]` に入る。 -/
theorem canonicalActualStraightSuffixStart_bounds
    {w : Word}
    {s t : ℕ}
    (hst : s ≤ t)
    (hTerminalPos : 0 < Word.criticalDefect w t) :
    s ≤ canonicalActualStraightSuffixStart w s t ∧
      canonicalActualStraightSuffixStart w s t ≤ t := by
  classical
  unfold canonicalActualStraightSuffixStart
  by_cases hNE : (actualStraightSuffixBadSet w s t).Nonempty
  · rw [dite_eq_left hNE]
    let m := (actualStraightSuffixBadSet w s t).max' hNE
    have hmMem : m ∈ actualStraightSuffixBadSet w s t := by
      dsimp [m]
      exact Finset.max'_mem _ _
    have hmSpec := (mem_actualStraightSuffixBadSet_iff w s t m).1 hmMem
    have hsm : s ≤ m := hmSpec.2.1
    have hmt : m < t := by
      have hmLe : m ≤ t := by omega
      by_contra hnot
      have hmEq : m = t := by
        omega
      rcases hmSpec.2.2 with hZero | hStep
      · have hZeroT :
          Word.criticalDefect w t = 0 := by
          rw [← hmEq]
          exact hZero
        exact (Nat.ne_of_gt hTerminalPos) hZeroT
      · omega
    exact ⟨by omega, by omega⟩
  · rw [dite_eq_right hNE]
    exact ⟨le_rfl, hst⟩

/-- canonical start 以後 terminal まで bad cut は存在しない。 -/
theorem not_mem_actualStraightSuffixBadSet_of_start_le
    {w : Word}
    {s t k : ℕ}
    (hStart : canonicalActualStraightSuffixStart w s t ≤ k) :
    k ∉ actualStraightSuffixBadSet w s t := by
  classical
  intro hkMem
  unfold canonicalActualStraightSuffixStart at hStart
  by_cases hNE : (actualStraightSuffixBadSet w s t).Nonempty
  · rw [dite_eq_left hNE] at hStart
    have hle :
        k ≤ (actualStraightSuffixBadSet w s t).max' hNE :=
      Finset.le_max' _ _ hkMem
    omega
  · exact hNE ⟨k, hkMem⟩

/-- canonical start 以後 terminal positive cut までは defect が全て正。 -/
theorem criticalDefect_pos_of_canonicalStraightSuffixStart
    {w : Word}
    {s t k : ℕ}
    (hst : s ≤ t)
    (hTerminalPos : 0 < Word.criticalDefect w t)
    (hStart : canonicalActualStraightSuffixStart w s t ≤ k)
    (hkt : k ≤ t) :
    0 < Word.criticalDefect w k := by
  have hBounds :=
    canonicalActualStraightSuffixStart_bounds
      (w := w) hst hTerminalPos
  have hsk : s ≤ k := le_trans hBounds.1 hStart
  by_contra hnot
  have hZero : Word.criticalDefect w k = 0 := Nat.eq_zero_of_not_pos hnot
  have hkBad : k ∈ actualStraightSuffixBadSet w s t :=
    (mem_actualStraightSuffixBadSet_iff w s t k).2
      ⟨by omega, hsk, Or.inl hZero⟩
  exact
    (not_mem_actualStraightSuffixBadSet_of_start_le hStart) hkBad

/-- canonical start から terminal 直前までは actual prefix depth が exact `+1`。 -/
theorem prefixTwoDepth_succ_eq_add_one_of_canonicalStraightSuffixStart
    {w : Word}
    {s t k : ℕ}
    (hst : s ≤ t)
    (hTerminalPos : 0 < Word.criticalDefect w t)
    (hStart : canonicalActualStraightSuffixStart w s t ≤ k)
    (hkt : k < t) :
    Word.prefixTwoDepth w (k + 1) =
      Word.prefixTwoDepth w k + 1 := by
  have hBounds :=
    canonicalActualStraightSuffixStart_bounds
      (w := w) hst hTerminalPos
  have hsk : s ≤ k := le_trans hBounds.1 hStart
  by_contra hne
  have hkBad : k ∈ actualStraightSuffixBadSet w s t :=
    (mem_actualStraightSuffixBadSet_iff w s t k).2
      ⟨by omega, hsk, Or.inr ⟨hkt, hne⟩⟩
  exact
    (not_mem_actualStraightSuffixBadSet_of_start_le hStart) hkBad

/-- actual canonical straight suffix の薄い geometry packet。 -/
structure CanonicalActualStraightSuffix
    (w : Word)
    (s t : ℕ) where
  start : ℕ
  start_ge : s ≤ start
  start_le_terminal : start ≤ t
  defect_pos :
    ∀ {k : ℕ},
      start ≤ k →
      k ≤ t →
      0 < Word.criticalDefect w k
  unit_prefix_step :
    ∀ {k : ℕ},
      start ≤ k →
      k < t →
      Word.prefixTwoDepth w (k + 1) =
        Word.prefixTwoDepth w k + 1

/-- bad-set max から canonical straight suffix packet を作る。 -/
noncomputable def canonicalActualStraightSuffix
    {w : Word}
    {s t : ℕ}
    (hst : s ≤ t)
    (hTerminalPos : 0 < Word.criticalDefect w t) :
    CanonicalActualStraightSuffix w s t where
  start := canonicalActualStraightSuffixStart w s t
  start_ge :=
    (canonicalActualStraightSuffixStart_bounds
      (w := w) hst hTerminalPos).1
  start_le_terminal :=
    (canonicalActualStraightSuffixStart_bounds
      (w := w) hst hTerminalPos).2
  defect_pos := by
    intro k hStart hkt
    exact criticalDefect_pos_of_canonicalStraightSuffixStart
      hst hTerminalPos hStart hkt
  unit_prefix_step := by
    intro k hStart hkt
    exact prefixTwoDepth_succ_eq_add_one_of_canonicalStraightSuffixStart
      hst hTerminalPos hStart hkt

/-! ## critical roof staircase -/

/-- Beatty index の一段増分は高々 `2`。 -/
private theorem bridge_beattyIndex_succ_le_add_two
    (n : ℕ) :
    beattyIndex (n + 1) ≤ beattyIndex n + 2 := by
  apply beattyIndex_le_of_upper
  have hUpper := beattyIndex_upper n
  have hMul :
      3 ^ n * 3 ≤
        2 ^ (beattyIndex n + 1) * 4 := by
    exact Nat.mul_le_mul hUpper (by norm_num)
  calc
    3 ^ (n + 1)
        = 3 ^ n * 3 := by rw [pow_succ]
    _ ≤ 2 ^ (beattyIndex n + 1) * 4 := hMul
    _ = 2 ^ ((beattyIndex n + 2) + 1) := by
      calc
        2 ^ (beattyIndex n + 1) * 4
            = 2 ^ (beattyIndex n + 1) * 2 ^ 2 := by norm_num
        _ = 2 ^ ((beattyIndex n + 1) + 2) := by rw [← pow_add]
        _ = 2 ^ ((beattyIndex n + 2) + 1) := by congr 1

/-- Beatty index の一段増分は exact に `1` または `2`。 -/
private theorem bridge_beattyIndex_succ_eq_add_one_or_two
    (n : ℕ) :
    beattyIndex (n + 1) = beattyIndex n + 1 ∨
      beattyIndex (n + 1) = beattyIndex n + 2 := by
  have hLower := beattyIndex_lt_succ n
  have hUpper := bridge_beattyIndex_succ_le_add_two n
  omega

/-- critical roof の一段増分も exact に `1` または `2`。 -/
private theorem criticalHeight_succ_eq_add_one_or_two
    (n : ℕ) :
    Word.criticalHeight (n + 1) = Word.criticalHeight n + 1 ∨
      Word.criticalHeight (n + 1) = Word.criticalHeight n + 2 := by
  rw [criticalHeight_eq_beattyIndex (n + 1), criticalHeight_eq_beattyIndex n]
  exact bridge_beattyIndex_succ_eq_add_one_or_two n

/--
FirstCrossing 内で actual prefix が `+1` なら critical defect は staircase `0/1` step。
-/
theorem criticalDefect_succ_eq_self_or_add_one_of_unitPrefix
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {k : ℕ}
    (hkNext : k + 1 < Word.oddSteps w)
    (hUnit :
      Word.prefixTwoDepth w (k + 1) =
        Word.prefixTwoDepth w k + 1) :
    Word.criticalDefect w (k + 1) = Word.criticalDefect w k ∨
      Word.criticalDefect w (k + 1) = Word.criticalDefect w k + 1 := by
  have hk : k < Word.oddSteps w := by omega
  have hDepth0 :=
    firstCrossing_prefixTwoDepth_le_criticalHeight_all_affineCuts C.2 hk
  have hDepth1 :=
    firstCrossing_prefixTwoDepth_le_criticalHeight_all_affineCuts C.2 hkNext
  have hRestore0 :
      Word.prefixTwoDepth w k + Word.criticalDefect w k =
        Word.criticalHeight k := by
    unfold Word.criticalDefect
    omega
  have hRestore1 :
      Word.prefixTwoDepth w (k + 1) + Word.criticalDefect w (k + 1) =
        Word.criticalHeight (k + 1) := by
    unfold Word.criticalDefect
    omega
  rcases criticalHeight_succ_eq_add_one_or_two k with hOne | hTwo
  · left
    omega
  · right
    omega

/-! ## normalized quotient recurrence -/

/--
Integral corridor の actual quotient は一般には actual prefix increment `e_k` を係数に持つ。
straight suffix ではこの exponent が `1` へ落ちる。
-/
theorem actualFerrersIntegralCorridor_recurrence
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (I : ActualFerrersIntegralCorridor w)
    {k : ℕ}
    (hStart : I.start ≤ k)
    (hk : k < Word.oddSteps w) :
    3 * I.q k =
      (2 : ℤ) ^
          (Word.prefixTwoDepth w (k + 1) - Word.prefixTwoDepth w k) *
        I.q (k + 1) +
      (2 : ℤ) ^ Word.criticalDefect w k - 1 := by
  have hkLe : k ≤ Word.oddSteps w := Nat.le_of_lt hk
  have hk1Le : k + 1 ≤ Word.oddSteps w := by omega
  have hStart1 : I.start ≤ k + 1 := by omega
  have hQ0 := I.q_spec hStart hkLe
  have hQ1 := I.q_spec hStart1 hk1Le
  have hTail := actualFerrersSuffixZ_step w hk
  have hColumn := actualFerrersColumnDeficitZ_eq_factor C.2 hk
  have hDepthLt :
      Word.prefixTwoDepth w k < Word.prefixTwoDepth w (k + 1) :=
    Word.prefixTwoDepth_lt_of_valid C.1
      (i := k) (j := k + 1) (by omega) hk1Le
  have hDepthSplit :
      Word.prefixTwoDepth w (k + 1) =
        Word.prefixTwoDepth w k +
          (Word.prefixTwoDepth w (k + 1) - Word.prefixTwoDepth w k) := by
    omega
  have hThreeSplit :
      Word.oddSteps w - k =
        (Word.oddSteps w - (k + 1)) + 1 := by
    omega
  rw [hQ0, hQ1, hColumn] at hTail
  rw [hDepthSplit, pow_add, hThreeSplit, pow_succ] at hTail
  let common : ℤ :=
    (2 : ℤ) ^ Word.prefixTwoDepth w k *
      (3 : ℤ) ^ (Word.oddSteps w - (k + 1))
  have hCommonNe : common ≠ 0 := by
    dsimp [common]
    positivity
  have hFactored :
      common * (3 * I.q k) =
        common *
          ((2 : ℤ) ^
              (Word.prefixTwoDepth w (k + 1) - Word.prefixTwoDepth w k) *
            I.q (k + 1) +
            (2 : ℤ) ^ Word.criticalDefect w k - 1) := by
    dsimp [common]
    ring_nf at hTail ⊢
    exact hTail
  exact mul_left_cancel₀ hCommonNe hFactored

/-- terminal positive endpoint では integral-corridor quotient は zero。 -/
theorem integralCorridor_q_terminalPositiveEndpoint_eq_zero
    {w : Word}
    (I : ActualFerrersIntegralCorridor w)
    (T : TerminalPositiveDefectData w)
    (hStart : I.start ≤ T.index + 1) :
    I.q (T.index + 1) = 0 := by
  have hEndLe : T.index + 1 ≤ Word.oddSteps w :=
    Nat.succ_le_iff.mpr T.index_lt
  have hSpec := I.q_spec hStart hEndLe
  have hZero := actualFerrersSuffixZ_terminalPositiveEndpoint_eq_zero T
  rw [hZero] at hSpec
  have hFactorNe :
      (2 : ℤ) ^ Word.prefixTwoDepth w (T.index + 1) *
          (3 : ℤ) ^ (Word.oddSteps w - (T.index + 1)) ≠ 0 := by
    positivity
  have hMul :
      ((2 : ℤ) ^ Word.prefixTwoDepth w (T.index + 1) *
          (3 : ℤ) ^ (Word.oddSteps w - (T.index + 1))) *
        I.q (T.index + 1) = 0 := by
    exact hSpec.symm
  exact (mul_eq_zero.mp hMul).resolve_left hFactorNe

/--
canonical actual straight suffix と integral quotient corridor から
free-base monotone Hensel chain を構成する exact bridge。
-/
noncomputable def CanonicalActualStraightSuffix.toFreeBaseMonotoneHenselChain
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    (I : ActualFerrersIntegralCorridor w)
    (T : TerminalPositiveDefectData w)
    (S : CanonicalActualStraightSuffix w I.start T.index) :
    FreeBaseMonotoneHenselChain where
  width := T.index + 1 - S.start
  width_pos := by
    have hle := S.start_le_terminal
    omega
  delta := fun i => Word.criticalDefect w (S.start + i)
  q := fun i => I.q (S.start + i)
  delta_pos := by
    intro i hi
    apply S.defect_pos
    · omega
    · omega
  delta_step := by
    intro i hi
    let k := S.start + i
    have hkStart : S.start ≤ k := by
      dsimp [k]
      omega
    have hkLtT : k < T.index := by
      dsimp [k]
      omega
    have hkNext : k + 1 < Word.oddSteps w := by
      have ht := T.index_lt
      omega
    have hUnit := S.unit_prefix_step hkStart hkLtT
    have hStep :=
      criticalDefect_succ_eq_self_or_add_one_of_unitPrefix C hkNext hUnit
    dsimp [k] at hStep
    simpa [Nat.add_assoc] using hStep
  q_terminal := by
    have hStartLeTerminal : S.start ≤ T.index :=
      S.start_le_terminal
    have hEnd :
        S.start + (T.index + 1 - S.start) = T.index + 1 := by
      omega
    change I.q (S.start + (T.index + 1 - S.start)) = 0
    rw [hEnd]
    apply integralCorridor_q_terminalPositiveEndpoint_eq_zero I T
    exact le_trans S.start_ge (by omega)
  recurrence := by
    intro i hi
    let k := S.start + i
    have hkStartS : S.start ≤ k := by
      dsimp [k]
      omega
    have hkStartI : I.start ≤ k := le_trans S.start_ge hkStartS
    have hkLtEndpoint : k < T.index + 1 := by
      dsimp [k]
      omega
    have hkLtP : k < Word.oddSteps w := by
      have ht := T.index_lt
      omega
    have hRec :=
      actualFerrersIntegralCorridor_recurrence C I hkStartI hkLtP
    by_cases hLast : k + 1 = T.index + 1
    · have hQNext : I.q (k + 1) = 0 := by
        rw [hLast]
        apply integralCorridor_q_terminalPositiveEndpoint_eq_zero I T
        exact le_trans S.start_ge (by omega)
      change
        3 * I.q k =
          2 * I.q (k + 1) +
            (2 : ℤ) ^ Word.criticalDefect w k - 1
      rw [hQNext] at hRec ⊢
      simpa only [mul_zero, zero_add] using hRec
    · have hkLtT : k < T.index := by omega
      have hUnit := S.unit_prefix_step hkStartS hkLtT
      have hDiff :
          Word.prefixTwoDepth w (k + 1) - Word.prefixTwoDepth w k = 1 := by
        omega
      change
        3 * I.q k =
          2 * I.q (k + 1) +
            (2 : ℤ) ^ Word.criticalDefect w k - 1
      rw [hDiff] at hRec
      norm_num at hRec
      exact hRec

/--
中心 lemma 4。

terminal defect even branch では、actual word + exact deficit order だけから
canonical positive straight suffix と、それに対応する
`FreeBaseMonotoneHenselChain` が存在する。

返す等式により chain の `delta/q` が actual Ferrers coordinates そのものであることを保持する。
-/
theorem exists_canonicalStraightHenselSuffix
    {w : Word}
    (C : ValidMinimalCrossingBlock w)
    {v : ℕ}
    (hOrder : ExactThreeAdicOrder (actualFerrersSuffixZ w 0) v)
    (hv : v ≤ Word.oddSteps w)
    (hEven :
      Word.criticalDefect w
          (terminalPositiveDefectDataOfExactOrder w hOrder).index % 2 = 0) :
    let T := terminalPositiveDefectDataOfExactOrder w hOrder
    ∃ S : CanonicalActualStraightSuffix
        w (Word.oddSteps w - v) T.index,
      ∃ H : FreeBaseMonotoneHenselChain,
        H.width = T.index + 1 - S.start ∧
        (∀ i : ℕ, H.delta i = Word.criticalDefect w (S.start + i)) ∧
        (∀ i : ℕ, H.q i =
          (actualFerrersIntegralCorridorOfThreeAdicOrder C hOrder hv).q
            (S.start + i)) := by
  intro T
  have hStartLt : Word.oddSteps w - v < T.index + 1 :=
    terminalDefect_even_implies_criticalization_lt_endpoint
      C T hOrder hv hEven
  have hStartLeT : Word.oddSteps w - v ≤ T.index := by omega
  let I : ActualFerrersIntegralCorridor w :=
    actualFerrersIntegralCorridorOfThreeAdicOrder C hOrder hv
  let S : CanonicalActualStraightSuffix w (Word.oddSteps w - v) T.index :=
    canonicalActualStraightSuffix hStartLeT T.positive
  let H : FreeBaseMonotoneHenselChain :=
    S.toFreeBaseMonotoneHenselChain C I T
  refine ⟨S, H, ?_, ?_, ?_⟩
  · rfl
  · intro i
    rfl
  · intro i
    rfl

end DoubleDecomposition
end CSTMicro
end Collatz2
