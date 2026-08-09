import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain
import CollatzLean.Collatz.OddOrbit.FutureMinimumLocal
import CollatzLean.Collatz.OneStep.Carry
import CollatzLean.Collatz.FiniteOrbit.Comparison

/-!
# canonical contracting chain の gap-depth dichotomy

bounded depth では shallow future minimum が隣接2点ごとに必ず現れる。
unbounded depth では valuation triangle を start-lower / equal-cancellation /
next-lower に分類し、aligned exponent-1 run の差深さ輸送から
captured / deferred / synchronized high-event 構造へ接続する。
-/

namespace Collatz
namespace AdjacentReturn

namespace CanonicalContractingChain

/-- chain 第 n gap depth。 -/
def gapDepth {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) : ℕ :=
  (C.valuationData n).gapDepth

/-- chain 第 n start `+1` depth。 -/
def startDepth {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) : ℕ :=
  (C.valuationData n).startDepth

/-- gap depths が M 以下で一様有界。 -/
def GapDepthBounded
    {O : OddOrbit} (C : CanonicalContractingChain O) (M : ℕ) : Prop :=
  ∀ n : ℕ, C.gapDepth n ≤ M

/-- gap depths が非有界。 -/
def GapDepthUnbounded
    {O : OddOrbit} (C : CanonicalContractingChain O) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < C.gapDepth n

/-- bounded / unbounded の完全二分岐。 -/
theorem gapDepth_bounded_or_unbounded
    {O : OddOrbit} (C : CanonicalContractingChain O) :
    (∃ M : ℕ, C.GapDepthBounded M) ∨ C.GapDepthUnbounded := by
  classical
  by_cases h : ∃ M : ℕ, C.GapDepthBounded M
  · exact Or.inl h
  · right
    intro M
    have hnot : ¬ C.GapDepthBounded M := by
      intro hM
      exact h ⟨M, hM⟩
    unfold GapDepthBounded at hnot
    push Not at hnot
    exact hnot

/-- 一つの valuation triangle の局所三分岐。 -/
inductive LocalGapDepthOutcome
    {O : OddOrbit} {R : State O} (V : State.ValuationData R) : Type
  | startLower
      (depth_lt : V.startDepth < V.nextDepth)
      (gap_eq : V.gapDepth = V.startDepth)
  | equalCancellation
      (depth_eq : V.startDepth = V.nextDepth)
      (depth_lt_gap : V.startDepth < V.gapDepth)
  | nextLower
      (depth_lt : V.nextDepth < V.startDepth)
      (gap_eq : V.gapDepth = V.nextDepth)

/-- valuation triangle を local three-way outcome へ分類。 -/
def classifyLocalGapDepth
    {O : OddOrbit} {R : State O}
    (V : State.ValuationData R) : LocalGapDepthOutcome V := by
  by_cases hAC : V.startDepth < V.nextDepth
  · exact
      LocalGapDepthOutcome.startLower hAC
        (V.gapDepth_eq_startDepth_of_lt hAC)
  · by_cases hEq : V.startDepth = V.nextDepth
    · exact
        LocalGapDepthOutcome.equalCancellation hEq
          (V.startDepth_lt_gapDepth_of_eq hEq)
    · have hCA : V.nextDepth < V.startDepth := by
        omega
      exact
        LocalGapDepthOutcome.nextLower hCA
          (V.gapDepth_eq_nextDepth_of_lt hCA)

/-- bounded gap depth なら隣接する二つの future-minimum depth の少なくとも一方は shallow。 -/
theorem shallow_pair_of_gapDepth_bounded
    {O : OddOrbit} (C : CanonicalContractingChain O)
    {M : ℕ} (hB : C.GapDepthBounded M) (n : ℕ) :
    (C.valuationData n).startDepth ≤ M ∨
      (C.valuationData n).nextDepth ≤ M := by
  let V := C.valuationData n
  have hgap : V.gapDepth ≤ M := by
    simpa [gapDepth, V] using hB n
  cases classifyLocalGapDepth V with
  | startLower hlt heq =>
      left
      rw [← heq]
      exact hgap
  | equalCancellation heq hlt =>
      left
      exact le_trans (Nat.le_of_lt hlt) hgap
  | nextLower hlt heq =>
      right
      rw [← heq]
      exact hgap

/-- bounded branch is syndetically shallow: n or n+1 start depth is ≤ M。 -/
theorem syndetic_shallow_of_gapDepth_bounded
    {O : OddOrbit} (C : CanonicalContractingChain O)
    {M : ℕ} (hB : C.GapDepthBounded M) (n : ℕ) :
    C.startDepth n ≤ M ∨ C.startDepth (n + 1) ≤ M := by
  rcases C.shallow_pair_of_gapDepth_bounded hB n with h | h
  · exact Or.inl h
  · right
    have hcoh := C.valuationDepth_coherent n
    unfold startDepth
    rw [← hcoh]
    exact h

/-- chain state start の canonical first-high data。 -/
noncomputable def startFirstHigh
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    OddOrbit.FutureMinimumFirstHighData
      (O := O) (C.state n).startIndex :=
  OddOrbit.FutureMinimumFirstHighData.firstHigh
    O (C.state n).startIndex

/-- chain state next future-minimum の first-high data。 -/
noncomputable def nextFirstHigh
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ) :
    OddOrbit.FutureMinimumFirstHighData (O := O) (C.state n).nextIndex :=
  OddOrbit.FutureMinimumFirstHighData.firstHigh O (C.state n).nextIndex

/-- shallow start では first high が M 未満に来て、その exponent も M 以下。 -/
theorem shallow_firstHigh_control
    {O : OddOrbit} (C : CanonicalContractingChain O)
    {M n : ℕ}
    (hshallow : (C.valuationData n).startDepth ≤ M) :
    (C.startFirstHigh n).offset < M ∧
      O.exponent
        ((C.state n).startIndex + (C.startFirstHigh n).offset) ≤ M ∧
      (O.segment
        (C.state n).startIndex
        ((C.startFirstHigh n).offset + 1)).Expanding := by
  let V := C.valuationData n
  let H := C.startFirstHigh n
  have hVshallow :
      V.startDepth ≤ M := by
    simpa [V] using hshallow
  have hdepth :
      V.startDepth = H.offset + 1 :=
    H.depth_eq_offset_add_one V.startFactor
  have hexp :
      O.exponent
          ((C.state n).startIndex + H.offset) ≤
        V.startDepth :=
    H.highExponent_le_depth
      (C.state n).startFutureMinimum
      (C.state n).unbounded
      V.startFactor
  have hExp :
      (O.segment
        (C.state n).startIndex
        (H.offset + 1)).Expanding :=
    H.prefixExpanding
      (C.state n).startFutureMinimum
      (C.state n).unbounded
  have hoffSucc :
      H.offset + 1 ≤ M := by
    rw [← hdepth]
    exact hVshallow
  have hoff :
      H.offset < M := by
    exact Nat.lt_of_succ_le
      (by simpa [Nat.succ_eq_add_one] using hoffSucc)
  have hexpM :
      O.exponent
          ((C.state n).startIndex + H.offset) ≤ M :=
    le_trans hexp hVshallow
  simpa [H] using
    And.intro hoff (And.intro hexpM hExp)


/--
bounded branch: arbitrarily long first crossings still occur at shallow starts。
したがって finite early-high type の後ろに arbitrarily long expanding continuation が残る。
-/
theorem arbitrarily_long_shallow_firstCrossing_of_gapDepth_bounded
    {O : OddOrbit} (C : CanonicalContractingChain O)
    {M : ℕ} (hB : C.GapDepthBounded M) :
    ∀ L : ℕ,
      ∃ n : ℕ,
        C.startDepth n ≤ M ∧
        ∀ F : FirstCrossingData (C.state n), L < F.length := by
  intro L
  obtain ⟨J, hJ⟩ := C.firstCrossing_lengths_tend_to_infinity L
  rcases C.syndetic_shallow_of_gapDepth_bounded hB J with h0 | h1
  · refine ⟨J, h0, ?_⟩
    intro F
    exact hJ J le_rfl F
  · refine ⟨J + 1, h1, ?_⟩
    intro F
    exact hJ (J + 1) (by omega) F

/-- equal cancellation itself splits into deep synchronization or moderate cancellation。 -/
theorem equalCancellation_huge_or_moderate
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ)
    (hEq : (C.valuationData n).startDepth =
      (C.valuationData n).nextDepth) :
    2 * (C.valuationData n).startDepth ≤
        (C.valuationData n).gapDepth ∨
      (C.valuationData n).gapDepth <
        2 * (C.valuationData n).startDepth := by
  omega

/-- moderate equal cancellation with a large gap forces a large start depth too。 -/
theorem startDepth_large_of_equal_moderate_largeGap
    {O : OddOrbit} (C : CanonicalContractingChain O) (n M : ℕ)
    (_hEq : (C.valuationData n).startDepth =
      (C.valuationData n).nextDepth)
    (hmoderate :
      (C.valuationData n).gapDepth <
        2 * (C.valuationData n).startDepth)
    (hlarge : M < (C.valuationData n).gapDepth) :
    M < 2 * (C.valuationData n).startDepth := by
  omega

/-- a segment whose exponents are all 1 equals a replicate-one word。 -/
private theorem segment_eq_replicate_one
    (O : OddOrbit) {start L : ℕ}
    (hones : ∀ k : ℕ, k < L → O.exponent (start + k) = 1) :
    O.segment start L = List.replicate L 1 := by
  induction L generalizing start with
  | zero => simp
  | succ L ih =>
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail :
          ∀ k : ℕ, k < L → O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        have hindex :
            start + 1 + k = start + (k + 1) := by
          omega
        rw [hindex]
        exact h
      rw [O.segment_succ, hfirst, ih htail]
      rfl

/--
aligned exponent-1 run of length L transports an initial gap depth E to E-L exactly。
-/
theorem aligned_oneRun_gapFactor
    {O : OddOrbit} {R : State O}
    (V : State.ValuationData R)
    {L : ℕ}
    (hL : L ≤ V.gapDepth)
    (hLower : ∀ k : ℕ, k < L →
      O.exponent (R.startIndex + k) = 1)
    (hUpper : ∀ k : ℕ, k < L →
      O.exponent (R.nextIndex + k) = 1) :
    TwoAdic.ExactFactor
      (O.value (R.nextIndex + L) - O.value (R.startIndex + L))
      (V.gapDepth - L)
      (3 ^ L * V.gapOddPart) := by
  have hLowWord := segment_eq_replicate_one O hLower
  have hUpWord := segment_eq_replicate_one O hUpper
  have hLowReal := O.realizesSegment R.startIndex L
  have hUpReal := O.realizesSegment R.nextIndex L
  rw [hLowWord] at hLowReal
  rw [hUpWord] at hUpReal
  have hDiff := hLowReal.difference hUpReal R.startValue_lt_nextValue.le
  have hDiff' :
      2 ^ L *
          (O.value (R.nextIndex + L) - O.value (R.startIndex + L)) =
        3 ^ L * R.valueGap := by
    simpa [Word.twoSteps, Word.oddSteps, State.startValue,
      State.nextValue, State.valueGap] using hDiff
  have hE :
      V.gapDepth = L + (V.gapDepth - L) := by
    exact (Nat.add_sub_of_le hL).symm
  have hpowSplit :
      2 ^ V.gapDepth =
        2 ^ L * 2 ^ (V.gapDepth - L) := by
    calc
      2 ^ V.gapDepth
          = 2 ^ (L + (V.gapDepth - L)) :=
        congrArg (fun t : ℕ => 2 ^ t) hE
      _ = 2 ^ L * 2 ^ (V.gapDepth - L) := by
        rw [pow_add]
  have hscaled :
      2 ^ L *
          (O.value (R.nextIndex + L) -
            O.value (R.startIndex + L)) =
        2 ^ L *
          (2 ^ (V.gapDepth - L) *
            (3 ^ L * V.gapOddPart)) := by
    calc
      2 ^ L *
          (O.value (R.nextIndex + L) -
            O.value (R.startIndex + L))
          = 3 ^ L * R.valueGap := hDiff'
      _ = 3 ^ L *
          (2 ^ V.gapDepth * V.gapOddPart) := by
            rw [V.gapFactor.1]
      _ = 2 ^ L *
          (2 ^ (V.gapDepth - L) *
            (3 ^ L * V.gapOddPart)) := by
            rw [hpowSplit]
            ring
  have hfactor :
      O.value (R.nextIndex + L) -
          O.value (R.startIndex + L) =
        2 ^ (V.gapDepth - L) *
          (3 ^ L * V.gapOddPart) :=
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega)) hscaled
  refine ⟨hfactor, ?_⟩
  have hthreeOdd : Odd (3 ^ L) := by
    exact (show Odd (3 : ℕ) by decide).pow
  exact hthreeOdd.mul V.gapFactor.2

/-- startDepth < nextDepth branch: first divergence is a depth-1 captured event。 -/
theorem startLower_firstDivergence_captured
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ)
    (hAC : (C.valuationData n).startDepth <
      (C.valuationData n).nextDepth) :
    let L := (C.startFirstHigh n).offset
    let x := O.value ((C.state n).startIndex + L)
    let y := O.value ((C.state n).nextIndex + L)
    ∃ u b : ℕ,
      TwoAdic.ExactFactor (y - x) 1 u ∧
      O.HighExponentAt ((C.state n).startIndex + L) ∧
      O.exponent ((C.state n).nextIndex + L) = 1 ∧
      TwoAdic.ExactFactor (3 * y + 1) 1 b := by
  classical
  let V := C.valuationData n
  let Hx := C.startFirstHigh n
  let Hy := C.nextFirstHigh n
  let L := Hx.offset
  have hgapEq : V.gapDepth = V.startDepth :=
    V.gapDepth_eq_startDepth_of_lt hAC
  have hxDepth : V.startDepth = Hx.offset + 1 :=
    Hx.depth_eq_offset_add_one V.startFactor
  have hyDepth : V.nextDepth = Hy.offset + 1 :=
    Hy.depth_eq_offset_add_one V.nextFactor
  have hAC' :
      V.startDepth < V.nextDepth := by
    simpa [V] using hAC
  have hOffset :
      Hx.offset < Hy.offset := by
    have h :
        Hx.offset + 1 < Hy.offset + 1 := by
      rw [← hxDepth, ← hyDepth]
      exact hAC'
    exact Nat.lt_of_succ_lt_succ
      (by simpa [Nat.succ_eq_add_one] using h)
  have hUpperOne :
      O.exponent
        ((C.state n).nextIndex + Hx.offset) = 1 :=
    Hy.beforeHigh_one Hx.offset hOffset
  have hLGap :
      Hx.offset ≤ V.gapDepth := by
    rw [hgapEq, hxDepth]
    omega
  let u : ℕ :=
    3 ^ Hx.offset * V.gapOddPart
  have hu :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + Hx.offset) -
          O.value ((C.state n).startIndex + Hx.offset))
        (V.gapDepth - Hx.offset)
        u := by
    simpa [u] using
      aligned_oneRun_gapFactor V hLGap
        Hx.beforeHigh_one
        (fun k hk =>
          Hy.beforeHigh_one k (lt_trans hk hOffset))
  have hdepthOne :
      V.gapDepth - Hx.offset = 1 := by
    rw [hgapEq, hxDepth]
    omega
  have huOne :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + Hx.offset) -
          O.value ((C.state n).startIndex + Hx.offset))
        1
        u := by
    rw [hdepthOne] at hu
    exact hu
  let x := O.value ((C.state n).startIndex + Hx.offset)
  let y := O.value ((C.state n).nextIndex + Hx.offset)
  have huPos : 0 < u := by
    rcases huOne.2 with ⟨k, hk⟩
    omega
  have hxyLt : x < y := by
    have hdiffPos : 0 < y - x := by
      rw [huOne.1]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) huPos
    exact Nat.sub_pos_iff_lt.mp hdiffPos
  have hxy : y = x + 2 ^ 1 * u := by
    have h := Nat.sub_add_cancel hxyLt.le
    rw [huOne.1] at h
    omega
  let e := O.exponent ((C.state n).startIndex + Hx.offset)
  have heTwo : 2 ≤ e := by
    have hHigh :
        O.HighExponentAt
          ((C.state n).startIndex + Hx.offset) :=
      Hx.high
    unfold OddOrbit.HighExponentAt at hHigh
    dsimp [e]
    omega
  let r := e - 1
  have hr : 0 < r := by dsimp [r]; omega
  have he : e = 1 + r := by dsimp [r]; omega
  let a := O.value ((C.state n).startIndex + Hx.offset + 1)
  have haOdd : Odd a := O.value_odd _
  have hstep : 3 * x + 1 = 2 ^ (1 + r) * a := by
    have hs := O.step ((C.state n).startIndex + Hx.offset)
    dsimp [x, a]
    rw [← he]
    exact hs.symm
  obtain ⟨b, hb⟩ :=
    OneStep.captured_of_depth_lt
      (x := x) (y := y) (d := 1) (r := r)
      (a := a) (u := u)
      hr hxy huOne.2 hstep
  refine ⟨u, b, ?_, ?_, ?_, hb⟩
  · simpa [x, y] using huOne
  · simpa [Hx, L] using Hx.high
  · simpa [Hy, Hx, L] using hUpperOne

/-- nextDepth < startDepth branch: first divergence is the deferred orientation。 -/
theorem nextLower_firstDivergence_deferred
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ)
    (hCA : (C.valuationData n).nextDepth <
      (C.valuationData n).startDepth) :
    let L := (C.nextFirstHigh n).offset
    let x := O.value ((C.state n).startIndex + L)
    let y := O.value ((C.state n).nextIndex + L)
    ∃ u q : ℕ,
      TwoAdic.ExactFactor (y - x) 1 u ∧
      O.exponent ((C.state n).startIndex + L) = 1 ∧
      O.HighExponentAt ((C.state n).nextIndex + L) ∧
      3 * y + 1 = 2 ^ 2 * q := by
  classical
  let V := C.valuationData n
  let Hx := C.startFirstHigh n
  let Hy := C.nextFirstHigh n
  let L := Hy.offset
  have hgapEq : V.gapDepth = V.nextDepth :=
    V.gapDepth_eq_nextDepth_of_lt hCA
  have hxDepth : V.startDepth = Hx.offset + 1 :=
    Hx.depth_eq_offset_add_one V.startFactor
  have hyDepth : V.nextDepth = Hy.offset + 1 :=
    Hy.depth_eq_offset_add_one V.nextFactor
  have hCA' :
      V.nextDepth < V.startDepth := by
    simpa [V] using hCA
  have hOffset :
      Hy.offset < Hx.offset := by
    have h :
        Hy.offset + 1 < Hx.offset + 1 := by
      rw [← hyDepth, ← hxDepth]
      exact hCA'
    exact Nat.lt_of_succ_lt_succ
      (by simpa [Nat.succ_eq_add_one] using h)
  have hLowerOne :
      O.exponent
        ((C.state n).startIndex + Hy.offset) = 1 :=
    Hx.beforeHigh_one Hy.offset hOffset
  have hLGap :
      Hy.offset ≤ V.gapDepth := by
    rw [hgapEq, hyDepth]
    omega
  let u : ℕ :=
    3 ^ Hy.offset * V.gapOddPart
  have hu :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + Hy.offset) -
          O.value ((C.state n).startIndex + Hy.offset))
        (V.gapDepth - Hy.offset)
        u := by
    simpa [u] using
      aligned_oneRun_gapFactor V hLGap
        (fun k hk =>
          Hx.beforeHigh_one k (lt_trans hk hOffset))
        Hy.beforeHigh_one
  have hdepthOne :
      V.gapDepth - Hy.offset = 1 := by
    rw [hgapEq, hyDepth]
    omega
  have huOne :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + Hy.offset) -
          O.value ((C.state n).startIndex + Hy.offset))
        1
        u := by
    rw [hdepthOne] at hu
    exact hu
  let x :=
    O.value ((C.state n).startIndex + Hy.offset)
  let y :=
    O.value ((C.state n).nextIndex + Hy.offset)
  have huPos : 0 < u := by
    rcases huOne.2 with ⟨k, hk⟩
    omega
  have hxyLt : x < y := by
    have hdiffPos : 0 < y - x := by
      rw [huOne.1]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) huPos
    exact Nat.sub_pos_iff_lt.mp hdiffPos
  have hxy : y = x + 2 ^ 1 * u := by
    have h := Nat.sub_add_cancel hxyLt.le
    rw [huOne.1] at h
    omega
  let a := O.value ((C.state n).startIndex + Hy.offset + 1)
  have haOdd : Odd a := O.value_odd _
  have hstep : 3 * x + 1 = 2 ^ 1 * a := by
    have hs := O.step ((C.state n).startIndex + Hy.offset)
    rw [hLowerOne] at hs
    simpa [x, a] using hs.symm
  obtain ⟨q, hq⟩ :=
    OneStep.deferred_of_depth_eq
      (x := x) (y := y) (d := 1)
      (a := a) (u := u)
      hxy huOne.2 hstep haOdd
  refine ⟨u, q, ?_, ?_, ?_, ?_⟩
  · simpa [x, y] using huOne
  · simpa [Hx, Hy, L] using hLowerOne
  · simpa [Hy, L] using Hy.high
  · simpa using hq

/--
equal-depth cancellation が `E ≥ 2A` まで深ければ first high step 自体も synchronized。
-/
theorem equalDepth_hugeGap_firstHigh_synchronized
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ)
    (hEq : (C.valuationData n).startDepth =
      (C.valuationData n).nextDepth)
    (hHuge :
      2 * (C.valuationData n).startDepth ≤
        (C.valuationData n).gapDepth) :
    let L := (C.startFirstHigh n).offset
    O.exponent ((C.state n).startIndex + L) =
      O.exponent ((C.state n).nextIndex + L) := by
  classical
  let V := C.valuationData n
  let Hx := C.startFirstHigh n
  let Hy := C.nextFirstHigh n
  have hxDepth : V.startDepth = Hx.offset + 1 :=
    Hx.depth_eq_offset_add_one V.startFactor
  have hyDepth : V.nextDepth = Hy.offset + 1 :=
    Hy.depth_eq_offset_add_one V.nextFactor
  have hEq' :
      V.startDepth = V.nextDepth := by
    simpa [V] using hEq
  have hHuge' :
      2 * V.startDepth ≤ V.gapDepth := by
    simpa [V] using hHuge
  have hOffsets :
      Hx.offset = Hy.offset := by
    have h :
        Hx.offset + 1 = Hy.offset + 1 := by
      rw [← hxDepth, ← hyDepth]
      exact hEq'
    exact Nat.add_right_cancel h
  let L := Hx.offset
  have hStartLeGap :
      V.startDepth ≤ V.gapDepth := by
    omega
  have hLStart :
      L < V.startDepth := by
    dsimp [L]
    rw [hxDepth]
    omega
  have hLGap :
      L ≤ V.gapDepth :=
    le_trans (Nat.le_of_lt hLStart) hStartLeGap
  have hDepthFactor₀ :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + L) -
          O.value ((C.state n).startIndex + L))
        (V.gapDepth - L)
        (3 ^ L * V.gapOddPart) := by
    apply aligned_oneRun_gapFactor V hLGap
    · intro k hk
      apply Hx.beforeHigh_one k
      simpa [L] using hk
    · intro k hk
      apply Hy.beforeHigh_one k
      have hkx : k < Hx.offset := by
        simpa [L] using hk
      rw [hOffsets] at hkx
      exact hkx
  let d := V.gapDepth - L
  have hDepthFactor :
      TwoAdic.ExactFactor
        (O.value ((C.state n).nextIndex + L) -
          O.value ((C.state n).startIndex + L))
        d
        (3 ^ L * V.gapOddPart) := by
    simpa [d] using hDepthFactor₀
  have hStartDepth :
      V.startDepth = L + 1 := by
    simpa [L] using hxDepth
  have hHugeL :
      2 * (L + 1) ≤ V.gapDepth := by
    rw [← hStartDepth]
    exact hHuge'
  have hAd :
      V.startDepth < d := by
    dsimp [d]
    rw [hStartDepth]
    omega
  let e := O.exponent ((C.state n).startIndex + L)
  have heLe : e ≤ V.startDepth := by
    have h := Hx.highExponent_le_depth
      (C.state n).startFutureMinimum
      (C.state n).unbounded
      V.startFactor
    simpa [e, L] using h
  have hed : e < d := lt_of_le_of_lt heLe hAd
  let x := O.value ((C.state n).startIndex + L)
  let y := O.value ((C.state n).nextIndex + L)
  let u' := 3 ^ L * V.gapOddPart
  let u' := 3 ^ L * V.gapOddPart
  have hGapOddPos :
      0 < V.gapOddPart := by
    rcases V.gapFactor.2 with ⟨k, hk⟩
    omega
  have huPos :
      0 < u' := by
    dsimp [u']
    exact Nat.mul_pos
      (Nat.pow_pos (by omega))
      hGapOddPos
  have hxyLt : x < y := by
    have hdiffPos : 0 < y - x := by
      rw [hDepthFactor.1]
      exact Nat.mul_pos (Nat.pow_pos (by omega)) huPos
    exact Nat.sub_pos_iff_lt.mp hdiffPos
  have hxy : y = x + 2 ^ d * u' := by
    have h := Nat.sub_add_cancel hxyLt.le
    rw [hDepthFactor.1] at h
    dsimp [u'] at h ⊢
    omega
  let a := O.value ((C.state n).startIndex + L + 1)
  have haOdd : Odd a := O.value_odd _
  have hxFactor : 3 * x + 1 = 2 ^ e * a := by
    have hs := O.step ((C.state n).startIndex + L)
    simpa [x, a, e] using hs.symm
  let S := OneStep.synchronized_of_depth_lt
    (x := x) (y := y) (d := d) (e := e)
    (a := a) (u := u')
    hed hxy hDepthFactor.2 hxFactor haOdd
  let e₂ := O.exponent ((C.state n).nextIndex + L)
  let b := O.value ((C.state n).nextIndex + L + 1)
  have hactualUpper :
      TwoAdic.ExactFactor (3 * y + 1) e₂ b := by
    refine ⟨?_, O.value_odd _⟩
    have hs := O.step ((C.state n).nextIndex + L)
    simpa [y, e₂, b] using hs.symm
  have heq : e = e₂ :=
    TwoAdic.exponent_unique S.upperFactor hactualUpper
  simpa [e, e₂, L] using heq


/-- equal-depth huge-gap synchronization leaves
  a strictly positive residual depth after the first high。 -/
theorem equalDepth_hugeGap_residualDepth_pos
    {O : OddOrbit} (C : CanonicalContractingChain O) (n : ℕ)
    (hEq : (C.valuationData n).startDepth =
      (C.valuationData n).nextDepth)
    (hHuge :
      2 * (C.valuationData n).startDepth ≤
        (C.valuationData n).gapDepth) :
    0 <
      (C.valuationData n).gapDepth -
        (C.startFirstHigh n).offset -
        O.exponent ((C.state n).startIndex + (C.startFirstHigh n).offset) := by
  let V := C.valuationData n
  let H := C.startFirstHigh n
  have hDepth : V.startDepth = H.offset + 1 :=
    H.depth_eq_offset_add_one V.startFactor
  have heLe :
      O.exponent ((C.state n).startIndex + H.offset) ≤ V.startDepth :=
    H.highExponent_le_depth
      (C.state n).startFutureMinimum
      (C.state n).unbounded
      V.startFactor
  dsimp [V, H] at hEq hHuge hDepth heLe ⊢
  omega

/-- unbounded branch supplies arbitrarily large local three-way witnesses。 -/
theorem arbitrarily_large_local_outcome
    {O : OddOrbit} (C : CanonicalContractingChain O)
    (hU : C.GapDepthUnbounded) (M : ℕ) :
    ∃ n : ℕ,
      M < C.gapDepth n ∧
      Nonempty (LocalGapDepthOutcome (C.valuationData n)) := by
  obtain ⟨n, hn⟩ := hU M
  exact ⟨n, hn, ⟨classifyLocalGapDepth (C.valuationData n)⟩⟩

end CanonicalContractingChain

end AdjacentReturn
end Collatz
