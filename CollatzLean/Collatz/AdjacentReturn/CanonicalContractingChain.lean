import CollatzLean.Collatz.AdjacentReturn.FullBlockCanonical
import CollatzLean.Collatz.AdjacentReturn.CanonicalLate
import CollatzLean.Collatz.Canonical.CylinderDynamics

/-!
# canonical 収縮連鎖

最終的に全区間が収縮する tail を十分先へずらし、各 full block が canonical、
各 first crossing も canonical、valuation も整合する連続 chain として保持する。
さらに固定 source からの累積した入れ子状の実際の word を構成する。
-/

namespace Collatz
namespace AdjacentReturn

/-- tail 上の任意の first-crossing family。 -/
structure EventuallyContractingFirstCrossingFamily
    {O : OddOrbit} (D : EventuallyContractingTailData O) where
  crossing : ∀ n : ℕ, FirstCrossingData (D.state n)

namespace EventuallyContractingFirstCrossingFamily

/-- 既存 tower API へ変換。 -/
def toTower
    {O : OddOrbit} {D : EventuallyContractingTailData O}
    (F : EventuallyContractingFirstCrossingFamily D) :
    ContractingFirstCrossingTower D.toContractingTower where
  crossing := by
    intro n
    simpa using F.crossing n

/-- tail 上の first-crossing の長さは無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {O : OddOrbit} {D : EventuallyContractingTailData O}
    (F : EventuallyContractingFirstCrossingFamily D) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      M < (F.crossing n).length := by
  intro M
  obtain ⟨J, hJ⟩ :=
    F.toTower.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro n hn
  have h := hJ n hn
  change M < (F.crossing n).length at h
  exact h

end EventuallyContractingFirstCrossingFamily

namespace EventuallyContractingTailData

/-- tail には全項の first crossing を同時に選んだ family が存在する。 -/
noncomputable def firstCrossingFamily
    {O : OddOrbit} (D : EventuallyContractingTailData O) :
    EventuallyContractingFirstCrossingFamily D := by
  classical
  refine ⟨fun n => Classical.choice ?_⟩
  exact (D.state n).existsFirstCrossingData (D.state_contracting n)

end EventuallyContractingTailData

/--
十分先へずらした canonical 収縮連鎖。
full block・first crossing・valuation を同時に保持する。
-/
structure CanonicalContractingChain (O : OddOrbit) where
  tail : EventuallyContractingTailData O
  shift : ℕ
  block : ∀ n : ℕ,
    CanonicalContractingBlockData (tail.state (shift + n))
  firstCrossingCanonical :
    ∀ n : ℕ,
    ∀ F : FirstCrossingData (tail.state (shift + n)),
      (tail.state (shift + n)).startValue =
        Word.canonicalStart
          ((tail.state (shift + n)).word.take F.length)
  valuation : ∀ n : ℕ,
    State.ValuationData (tail.state (shift + n))

namespace CanonicalContractingChain

/-- chain の第 n adjacent state。 -/
def state {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    State O :=
  C.tail.state (C.shift + n)

/-- chain の block データ。 -/
theorem blockData {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    CanonicalContractingBlockData (C.state n) := by
  simpa [state] using C.block n

/-- chain の valuation データ。 -/
def valuationData {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    State.ValuationData (C.state n) := by
  simpa [state] using C.valuation n

/-- 連続する chain state は正確に接続する。 -/
theorem nextValue_eq_next_startValue
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    (C.state n).nextValue = (C.state (n + 1)).startValue := by
  have h := C.tail.nextValue_eq_next_startValue (C.shift + n)
  simpa [state, Nat.add_assoc] using h

/-- chain の valuation depth は隣接 block 間で整合する。 -/
theorem valuationDepth_coherent
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    (C.valuationData n).nextDepth =
      (C.valuationData (n + 1)).startDepth := by
  let V := C.valuationData n
  let W := C.valuationData (n + 1)
  have hvalue :
      (C.state n).nextValue + 1 =
        (C.state (n + 1)).startValue + 1 := by
    rw [C.nextValue_eq_next_startValue n]
  have hW :
      TwoAdic.ExactFactor
        ((C.state n).nextValue + 1)
        W.startDepth W.startOddPart := by
    rw [hvalue]
    exact W.startFactor
  exact TwoAdic.exponent_unique V.nextFactor hW


/-- chain 上の任意の first-crossing 長も無限大へ進む。 -/
theorem firstCrossing_lengths_tend_to_infinity
    {O : OddOrbit} (C : CanonicalContractingChain O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n →
      ∀ F : FirstCrossingData (C.state n), M < F.length := by
  intro M
  let G : EventuallyContractingFirstCrossingFamily C.tail :=
    C.tail.firstCrossingFamily
  obtain ⟨J, hJ⟩ := G.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro n hn F
  have hchosen : M < (G.crossing (C.shift + n)).length :=
    hJ (C.shift + n) (by omega)
  have hEq : F.length = (G.crossing (C.shift + n)).length :=
    F.length_unique (G.crossing (C.shift + n))
  rw [hEq]
  exact hchosen

/-- chain の future-minimum depth は2以上。 -/
theorem startDepth_two_le
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    2 ≤ (C.valuationData n).startDepth :=
  (C.valuationData n).startDepth_two_le

/-- chain の gap depth は2以上。 -/
theorem gapDepth_two_le
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    2 ≤ (C.valuationData n).gapDepth :=
  (C.valuationData n).gapDepth_two_le

/-- chain の adjacent 値差は4の正の倍数。 -/
theorem valueGap_four_dvd
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    ∃ q : ℕ, (C.state n).valueGap = 4 * q :=
  (C.state n).valueGap_four_dvd

/-- full block は canonical な実際の run である。 -/
theorem blockRuns
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    Word.Runs
      (C.state n).word
      (C.state n).startValue
      (C.state n).nextValue := by
  exact (C.state n).word_valid.runs_of_realizes
    (C.state n).realizes
    (O.value_odd (C.state n).nextIndex)

/-- first crossing の canonical endpoint も実際の endpoint と一致する。 -/
theorem firstCrossingEndpoint_eq_canonicalEnd
    {O : OddOrbit} (C : CanonicalContractingChain O)
    (n : ℕ)
    (F : FirstCrossingData (C.state n)) :
    F.endpointValue =
      Word.canonicalEnd ((C.state n).word.take F.length) := by
  let Q : Word.ReplayCoordinate
      ((C.state n).word.take F.length)
      (C.state n).startValue
      F.endpointValue :=
    F.replayCoordinate
  have hstart :
      (C.state n).startValue =
        Word.canonicalStart ((C.state n).word.take F.length) := by
    simpa [state] using C.firstCrossingCanonical n F
  have hq : Q.quotient = 0 :=
    Q.quotient_eq_zero_of_start_eq_canonical hstart
  have hfinish := Q.finish_eq
  rw [hq] at hfinish
  simpa using hfinish

/-- 各 canonical first crossing は真の正 return を持つ C3 型有限 run である。 -/
theorem firstCrossing_positive_canonical
    {O : OddOrbit} (C : CanonicalContractingChain O)
    (n : ℕ) (F : FirstCrossingData (C.state n)) :
    (C.state n).startValue =
        Word.canonicalStart ((C.state n).word.take F.length) ∧
      F.endpointValue =
        Word.canonicalEnd ((C.state n).word.take F.length) ∧
      (C.state n).startValue < F.endpointValue := by
  refine ⟨?_, firstCrossingEndpoint_eq_canonicalEnd C n F, F.start_lt_endpoint⟩
  simpa [state] using C.firstCrossingCanonical n F

/-- chain の各 block は狭義の future-minimum corridor を満たす。 -/
theorem corridor
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    2 * ((C.state n).nextValue + 1) <
      3 * ((C.state n).startValue + 1) :=
  (C.state n).two_mul_nextValue_add_one_lt_three_mul_startValue_add_one
    (C.blockData n).contracting

/-- 累積入れ子 chain の固定 source。 -/
def source {O : OddOrbit} (C : CanonicalContractingChain O) : ℕ :=
  (C.state 0).startValue

/-- 先頭 n 個の adjacent block を連結した word。 -/
def cumulativeWord {O : OddOrbit} (C : CanonicalContractingChain O) :
    ℕ → Collatz.Word
  | 0 => []
  | n + 1 => C.cumulativeWord n ++ (C.state n).word

@[simp] theorem cumulativeWord_zero
    {O : OddOrbit} (C : CanonicalContractingChain O) :
    C.cumulativeWord 0 = [] := rfl

@[simp] theorem cumulativeWord_succ
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    C.cumulativeWord (n + 1) =
      C.cumulativeWord n ++ (C.state n).word := rfl

/-- 累積 word は固定された最初の source からの実際の run を与える。 -/
theorem cumulativeRuns
    {O : OddOrbit} (C : CanonicalContractingChain O) :
    ∀ n : ℕ,
      Word.Runs
        (C.cumulativeWord n)
        C.source
        (C.state n).startValue := by
  intro n
  induction n with
  | zero =>
      simpa [source] using Word.Runs.nil C.source
  | succ n ih =>
      rw [cumulativeWord_succ]
      have h := ih.append (blockRuns C n)
      rw [C.nextValue_eq_next_startValue n] at h
      exact h

/-- 累積入れ子 word の長さは block 数以上。 -/
theorem cumulativeWord_length_ge
    {O : OddOrbit} (C : CanonicalContractingChain O) :
    ∀ n : ℕ, n ≤ (C.cumulativeWord n).length := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cumulativeWord_succ, List.length_append]
      have hpos := (C.state n).length_pos
      rw [(C.state n).word_length]
      omega

/-- 累積入れ子 word は少なくとも n 個の total two-step を消費する。 -/
theorem cumulativeWord_twoSteps_ge
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    n ≤ (C.cumulativeWord n).twoSteps := by
  have hvalid := (C.cumulativeRuns n).valid
  have hlen := C.cumulativeWord_length_ge n
  have hsteps :=
    Word.oddSteps_le_twoSteps hvalid
  unfold Word.oddSteps at hsteps
  exact le_trans hlen hsteps

private theorem nat_lt_twoPow_succ (n : ℕ) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
      omega

/-- block 数が固定 source 以上になれば、累積 word も canonical になる。 -/
theorem cumulativeStart_eq_canonical_of_source_le
    {O : OddOrbit} (C : CanonicalContractingChain O)
    (n : ℕ) (hn : C.source ≤ n) :
    C.source = (C.cumulativeWord n).canonicalStart := by
  have hsourcePow : C.source < 2 ^ (n + 1) := by
    exact lt_of_lt_of_le
      (nat_lt_twoPow_succ C.source)
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega))
  have htwo := C.cumulativeWord_twoSteps_ge n
  have hpowLe :
      2 ^ (n + 1) ≤
        2 ^ ((C.cumulativeWord n).twoSteps + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  have hlt :
      C.source < (C.cumulativeWord n).residueModulus := by
    calc
      C.source < 2 ^ (n + 1) := hsourcePow
      _ ≤ 2 ^ ((C.cumulativeWord n).twoSteps + 1) := hpowLe
      _ = (C.cumulativeWord n).residueModulus := by
        simp [Word.residueModulus]
  exact (C.cumulativeRuns n).realizes.eq_canonicalStart_of_lt_modulus
    (O.value_odd (C.state n).startIndex) hlt

/-- 累積 word の canonical endpoint は chain の第 n future minimum である。 -/
theorem cumulativeEnd_eq_canonical_of_source_le
    {O : OddOrbit} (C : CanonicalContractingChain O)
    (n : ℕ) (hn : C.source ≤ n) :
    (C.state n).startValue =
      (C.cumulativeWord n).canonicalEnd := by
  have hstart := C.cumulativeStart_eq_canonical_of_source_le n hn
  let Q : Word.ReplayCoordinate
      (C.cumulativeWord n)
      C.source
      (C.state n).startValue :=
    Word.ReplayCoordinate.ofRealization
      (C.cumulativeRuns n).realizes
      (O.value_odd (C.state n).startIndex)
  have hq : Q.quotient = 0 :=
    Q.quotient_eq_zero_of_start_eq_canonical hstart
  have hfinish := Q.finish_eq
  rw [hq] at hfinish
  simpa using hfinish

/--
Baker 入力のもと、最終的に全区間が収縮する tail から canonical chain を構成する。
-/
noncomputable def ofEventuallyContractingTail
    {O : OddOrbit}
    (D : EventuallyContractingTailData O)
    (hGap : External.TwoThreeGapPolynomialBound) :
    CanonicalContractingChain O := by
  classical
  let G : EventuallyContractingFirstCrossingFamily D :=
    D.firstCrossingFamily
  let hBlockExists :=
    D.blocks_eventually_canonical hGap
  let Jblock : ℕ :=
    Classical.choose hBlockExists
  have hblock :
      ∀ n : ℕ,
        Jblock ≤ n →
          CanonicalContractingBlockData (D.state n) := by
    exact Classical.choose_spec hBlockExists
  let hQExists :=
    FirstCrossingData.replayQuotient_eq_zero_eventually hGap
  let Nq : ℕ :=
    Classical.choose hQExists
  have hqZero :
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        Nq ≤ F.length →
          F.replayCoordinate.quotient = 0 := by
    exact Classical.choose_spec hQExists
  let hCrossExists :=
    G.lengths_tend_to_infinity Nq
  let Jcross : ℕ :=
    Classical.choose hCrossExists
  have hcross :
      ∀ n : ℕ,
        Jcross ≤ n →
          Nq < (G.crossing n).length := by
    exact Classical.choose_spec hCrossExists
  let J := max Jblock Jcross
  refine {
    tail := D
    shift := J
    block := ?_
    firstCrossingCanonical := ?_
    valuation := ?_
  }
  · intro n
    exact hblock (J + n) (by
      dsimp [J]
      exact le_trans (Nat.le_max_left Jblock Jcross)
        (Nat.le_add_right (max Jblock Jcross) n))
  · intro n F
    have hJcross :
        Jcross ≤ J + n := by
      dsimp [J]
      exact le_trans
        (Nat.le_max_right Jblock Jcross)
        (Nat.le_add_right (max Jblock Jcross) n)
    have hGlen :
        Nq < (G.crossing (J + n)).length :=
      hcross (J + n) hJcross
    have hlenEq :
        F.length = (G.crossing (J + n)).length :=
      F.length_unique (G.crossing (J + n))
    have hlen :
        Nq ≤ F.length := by
      rw [hlenEq]
      exact Nat.le_of_lt hGlen
    have hzero :=
      hqZero O (D.state (J + n)) F hlen
    exact
      F.replayCoordinate.start_eq_canonical_of_quotient_eq_zero
        hzero
  · intro n
    exact
      Classical.choice
        (D.state (J + n)).existsValuationData

end CanonicalContractingChain

end AdjacentReturn
end Collatz
