import CollatzLean.Collatz2.Canonical.EndpointFloorBestUpperReduction
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper
import CollatzLean.Collatz2.Arithmetic.ExponentSlope

/-!
# Collatz2 Canonical: primitive reduced branch の record descent

Stage 3。

Stage 1--2 で original exponent pair が primitive + StripReduced に残った branch を扱う。
current A の任意 proper cut `a` 以後の suffix は contracting なので、その suffix の
最初の FirstCrossing length `r` を取る。

cut rotation

  rho_a = drop a w ++ take a w

に対し、wrap 前では exact に

  d_rho_a(r) = d_w(a+r) - d_w(a)

となる。

crossing では

* rank drop
* wide strip

の二択だが、StripReduced は wide strip を排除する。
さらに primitive `gcd(H,p)=1` は equality rank を排除するため、必ず strict rank descent

  d_(a+r) < d_a

を得る。

開始 rank が `0 < d_a < p` なら crossing block は最小 contracting depth

  twoSteps(block) = criticalHeight(r) + 1

を強制する。interior endpoint も再び critical roof 上に乗るので、この one-step packet は
well-founded に反復できる。
-/

namespace Collatz2
namespace Word

/-- prefix depth の add/drop 分解。 -/
private theorem take_add_eq_take_append_drop_take
    {α : Type*}
    (w : List α)
    (a r : ℕ) :
    w.take (a + r) =
      w.take a ++ (w.drop a).take r := by
  induction a generalizing w with
  | zero => simp
  | succ a ih =>
      cases w with
      | nil => simp
      | cons x w =>
          simp [Nat.succ_add, ih]

/-- cumulative two-depth の add/drop 分解。 -/
theorem prefixTwoDepth_add
    (w : Word)
    (a r : ℕ) :
    prefixTwoDepth w (a + r) =
      prefixTwoDepth w a + twoSteps ((w.drop a).take r) := by
  unfold prefixTwoDepth
  rw [take_add_eq_take_append_drop_take]
  exact twoSteps_append _ _

/-- terminal chord rank は signed / natural とも zero。 -/
@[simp] theorem chordRankInt_terminal_eq_zero
    (w : Word) :
    chordRankInt w (oddSteps w) = 0 := by
  unfold chordRankInt prefixTwoDepth oddSteps
  simp [mul_comm]

@[simp] theorem chordRank_terminal_eq_zero
    (w : Word) :
    chordRank w (oddSteps w) = 0 := by
  unfold chordRank prefixTwoDepth oddSteps
  simp [mul_comm]

/-- FirstCrossing では terminal 以前の signed rank は nonnegative。 -/
theorem FirstCrossing.chordRankInt_nonneg_of_pos_le
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLe : k ≤ oddSteps w) :
    0 ≤ chordRankInt w k := by
  by_cases hkEq : k = oddSteps w
  · subst k
    simp
  · have hkLt : k < oddSteps w := by omega
    rw [hF.chordRankInt_eq_natCast hkPos hkLt]
    exact_mod_cast (Nat.zero_le (chordRank w k))

end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
Stage 2 bridge: current A の exponent pair は、すでに primitive+reduced であるか、
より小さい denominator の primitive+reduced pair へ slope を上げず正規化できる。
-/
theorem primitiveReduced_or_exists_smallerNormalizedPair
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    D.exponentPair.PrimitiveReducedData ∨
      ∃ Q : Word.ContractingExponentPair,
        Q.PrimitiveReducedData ∧
        Q.oddCount < D.exponentPair.oddCount ∧
        Word.ContractingExponentPair.SlopeBelow Q D.exponentPair :=
  D.exponentPair.primitiveReduced_or_exists_strict_normalization

/-- current A の base FirstCrossing を word 名で読む。 -/
theorem wordFirstCrossing
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.FirstCrossing D.word := by
  simpa [word] using D.firstCrossing

/-- arbitrary cut rotation の prefix depth は suffix の同 prefix depth。 -/
theorem cutRotation_prefixTwoDepth
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {a r : ℕ}
    (hr : r ≤ (D.cutSuffix a).length) :
    Word.prefixTwoDepth (D.cutRotation a) r =
      Word.twoSteps ((D.cutSuffix a).take r) := by
  unfold Word.prefixTwoDepth cutRotation
  rw [List.take_append_of_le_length hr]

/-- cut rotation は whole と同じ odd-step 数。 -/
theorem cutRotation_oddSteps_eq
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (a : ℕ) :
    Word.oddSteps (D.cutRotation a) = Word.oddSteps D.word := by
  rw [D.cutRotation_eq_cyclicRotate]
  exact Word.oddSteps_cyclicRotate D.word a

/-- cut rotation は whole と同じ total two-depth。 -/
theorem cutRotation_twoSteps_eq
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (a : ℕ) :
    Word.twoSteps (D.cutRotation a) = Word.twoSteps D.word := by
  rw [D.cutRotation_eq_cyclicRotate]
  exact Word.twoSteps_cyclicRotate D.word a

/-- arbitrary cut の chord-rank shift。 -/
theorem cutRotation_rank_shift
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {a r : ℕ}
    (hr : r ≤ (D.cutSuffix a).length) :
    Word.chordRankInt (D.cutRotation a) r =
      Word.chordRankInt D.word (a + r) -
        Word.chordRankInt D.word a := by
  have hDepthRot := D.cutRotation_prefixTwoDepth hr
  have hDepthAdd := Word.prefixTwoDepth_add D.word a r
  have hOdd := D.cutRotation_oddSteps_eq a
  have hTwo := D.cutRotation_twoSteps_eq a
  unfold Word.chordRankInt
  rw [hOdd, hTwo, hDepthRot, hDepthAdd]
  push_cast
  ring_nf
  rfl

/-- arbitrary cut rotation rank の whole-coefficient formula。 -/
theorem cutRotation_rank_formula
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {a r : ℕ}
    (hr : r ≤ (D.cutSuffix a).length) :
    Word.chordRankInt (D.cutRotation a) r =
      (Word.twoSteps D.word : ℤ) * (r : ℤ) -
        (Word.oddSteps D.word : ℤ) *
          (Word.twoSteps ((D.cutSuffix a).take r) : ℤ) := by
  have hDepthRot := D.cutRotation_prefixTwoDepth hr
  have hOdd := D.cutRotation_oddSteps_eq a
  have hTwo := D.cutRotation_twoSteps_eq a
  unfold Word.chordRankInt
  rw [hOdd, hTwo, hDepthRot]

/--
current A の任意 proper cut から得る local record trap。
-/
structure CutRecordTrapData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (cutIndex : ℕ) where
  cutIndex_pos : 0 < cutIndex
  cutIndex_lt : cutIndex < Word.oddSteps D.word

  crossingLength : ℕ
  crossingLength_pos : 0 < crossingLength
  crossingLength_le_suffix :
    crossingLength ≤ (D.cutSuffix cutIndex).length

  firstCrossing :
    Word.FirstCrossing
      ((D.cutSuffix cutIndex).take crossingLength)

  before_record :
    ∀ j : ℕ,
      0 < j →
      j < crossingLength →
      Word.chordRankInt D.word cutIndex <
        Word.chordRankInt D.word (cutIndex + j)

  crossing_rank_or_strip :
    Word.chordRankInt D.word (cutIndex + crossingLength) ≤
        Word.chordRankInt D.word cutIndex ∨
      Word.oddSteps D.word <
        Word.stripRank D.word crossingLength

  next_le_terminal :
    cutIndex + crossingLength ≤ Word.oddSteps D.word

namespace CutRecordTrapData

/-- next cut index。 -/
def nextIndex
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) : ℕ :=
  a + R.crossingLength

/-- crossing block。 -/
def block
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) : Word :=
  (D.cutSuffix a).take R.crossingLength

@[simp] theorem block_eq
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    R.block = (D.cutSuffix a).take R.crossingLength := rfl

/-- next index は start より strict に後。 -/
theorem cutIndex_lt_nextIndex
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    a < R.nextIndex := by
  unfold nextIndex
  exact Nat.lt_add_of_pos_right R.crossingLength_pos

/-- crossing length は whole denominator より strict に小さい。 -/
theorem crossingLength_lt_whole
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    R.crossingLength < Word.oddSteps D.word := by
  have := R.next_le_terminal
  have ha := R.cutIndex_pos
  omega

end CutRecordTrapData

/--
Stage 3a: current A の任意 proper cut で rank trap を構成する。
-/
noncomputable def toCutRecordTrapData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (a : ℕ)
    (haPos : 0 < a)
    (haLt : a < Word.oddSteps D.word) :
    CutRecordTrapData D a := by
  classical
  have haLtLen : a < D.word.length := by
    simpa [Word.oddSteps] using haLt
  have hSuffixValid : Word.Valid (D.cutSuffix a) := by
    have hWhole :
        Word.Valid (D.word.take a ++ D.word.drop a) := by
      simpa using D.word_valid
    simpa [cutSuffix] using hWhole.suffix
  have haLtD : a < D.length := by
    rw [← D.word_length]
    exact haLtLen
  have hSuffixNe : D.cutSuffix a ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [cutSuffix, haLtD]
  have hSuffixC : Word.Contracting (D.cutSuffix a) := by
    have haLtD : a < D.length := by
      simpa [Word.oddSteps, D.word_length] using haLt
    exact D.cutSuffix_contracting haLtD
  have hExists :=
    Word.exists_firstCrossing_of_contracting
      hSuffixValid hSuffixNe hSuffixC
  let r : ℕ := Classical.choose hExists
  have hSpec := Classical.choose_spec hExists
  have hrLe : r ≤ (D.cutSuffix a).length := hSpec.1
  have hFirst :
      Word.FirstCrossing ((D.cutSuffix a).take r) := hSpec.2
  have hrPos : 0 < r := by
    have hTakeLen : ((D.cutSuffix a).take r).length = r :=
      List.length_take_of_le hrLe
    have hPos : 0 < ((D.cutSuffix a).take r).length :=
      List.length_pos_iff.mpr hFirst.nonempty
    rw [hTakeLen] at hPos
    exact hPos
  have hRhoC : Word.Contracting (D.cutRotation a) := by
    apply (Word.contracting_iff_threePow_lt_twoPow).2
    have h :=
      (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
    rw [D.cutRotation_oddSteps_eq, D.cutRotation_twoSteps_eq]
    exact h
  have hBefore :
      ∀ j : ℕ,
        0 < j →
        j < r →
        Word.chordRankInt D.word a <
          Word.chordRankInt D.word (a + j) := by
    intro j hjPos hjLt
    have hjLeSuffix : j ≤ (D.cutSuffix a).length :=
      Nat.le_trans (Nat.le_of_lt hjLt) hrLe
    have hTakeLen : ((D.cutSuffix a).take r).length = r :=
      List.length_take_of_le hrLe
    have hjLtTake : j < ((D.cutSuffix a).take r).length := by
      rw [hTakeLen]
      exact hjLt
    have hExpRaw := hFirst.properExpanding hjPos hjLtTake
    have hTakeTake :
        ((D.cutSuffix a).take r).take j =
          (D.cutSuffix a).take j := by
      simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
    rw [hTakeTake] at hExpRaw
    have hRhoTake :
        (D.cutRotation a).take j =
          (D.cutSuffix a).take j := by
      unfold cutRotation
      exact List.take_append_of_le_length hjLeSuffix
    have hExp : Word.Expanding ((D.cutRotation a).take j) := by
      rw [hRhoTake]
      exact hExpRaw
    have hjLtRho : j < (D.cutRotation a).length := by
      have hSuffixLe :
          (D.cutSuffix a).length ≤ (D.cutRotation a).length := by
        simp [cutRotation]
      omega
    have hRankRho :
        0 < Word.chordRankInt (D.cutRotation a) j :=
      Word.chordRankInt_pos_of_expanding_contracting
        hjPos hjLtRho hExp hRhoC
    have hShift :=
      D.cutRotation_rank_shift hjLeSuffix
    linarith
  have hCrossDichotomy :
      Word.chordRankInt D.word (a + r) ≤
          Word.chordRankInt D.word a ∨
        Word.oddSteps D.word < Word.stripRank D.word r := by
    have hrLeRho : r ≤ (D.cutRotation a).length := by
      have hSuffixLe :
          (D.cutSuffix a).length ≤ (D.cutRotation a).length := by
        simp [cutRotation]
      exact le_trans hrLe hSuffixLe
    have hRhoTake :
        (D.cutRotation a).take r =
          (D.cutSuffix a).take r := by
      unfold cutRotation
      exact List.take_append_of_le_length hrLe
    have hCrossC : Word.Contracting ((D.cutRotation a).take r) := by
      rw [hRhoTake]
      exact hFirst.terminalContracting
    have hShift := D.cutRotation_rank_shift  hrLe
    by_cases hNonpos : Word.chordRankInt (D.cutRotation a) r ≤ 0
    · left
      linarith
    · right
      have hRankPos : 0 < Word.chordRankInt (D.cutRotation a) r := by
        omega
      have hpRho : 0 < Word.oddSteps (D.cutRotation a) := by
        rw [D.cutRotation_oddSteps_eq]
        exact D.exponentPair.oddCount_pos
      have hStripRho :=
        Word.stripRank_gt_oddSteps_of_contracting_take_of_rankInt_pos
          hpRho hrPos hrLeRho hCrossC hRankPos
      simpa [Word.stripRank,
        D.cutRotation_oddSteps_eq,
        D.cutRotation_twoSteps_eq] using hStripRho
  have hNextLe : a + r ≤ Word.oddSteps D.word := by
    have hLenDrop :
        (D.cutSuffix a).length = D.word.length - a := by
      simp [cutSuffix]
    rw [hLenDrop] at hrLe
    simpa [Word.oddSteps] using (show a + r ≤ D.word.length by omega)
  exact {
    cutIndex_pos := haPos
    cutIndex_lt := haLt
    crossingLength := r
    crossingLength_pos := hrPos
    crossingLength_le_suffix := hrLe
    firstCrossing := hFirst
    before_record := hBefore
    crossing_rank_or_strip := hCrossDichotomy
    next_le_terminal := hNextLe
  }

namespace CutRecordTrapData

/-- primitive + reduced branch では crossing rank は strict に下がる。 -/
theorem crossingRank_strict_of_primitive_reduced
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    Word.chordRankInt D.word R.nextIndex <
      Word.chordRankInt D.word a := by
  have hrLtWhole : R.crossingLength < Word.oddSteps D.word :=
    R.crossingLength_lt_whole
  have hLe :
      Word.chordRankInt D.word R.nextIndex ≤
        Word.chordRankInt D.word a := by
    rcases R.crossing_rank_or_strip with hRank | hStrip
    · simpa [nextIndex] using hRank
    · have hPairReduced :=
        hReduced R.crossingLength R.crossingLength_pos hrLtWhole
      have hEq := D.exponentPair_stripRank_eq R.crossingLength
      rw [hEq] at hPairReduced
      have hOddCount :
          D.exponentPair.oddCount = Word.oddSteps D.word := by
        rfl
      rw [hOddCount] at hPairReduced
      omega
  have hNe :
      Word.chordRankInt D.word R.nextIndex ≠
        Word.chordRankInt D.word a := by
    intro hEqRank
    have hShift :=
      D.cutRotation_rank_shift R.crossingLength_le_suffix
    have hRotZero :
        Word.chordRankInt (D.cutRotation a) R.crossingLength = 0 := by
      rw [hShift]
      apply sub_eq_zero.mpr
      simpa [nextIndex] using hEqRank
    have hOdd := D.cutRotation_oddSteps_eq a
    have hTwo := D.cutRotation_twoSteps_eq a
    unfold Word.chordRankInt at hRotZero
    rw [hOdd, hTwo] at hRotZero
    have hEqZ :
        (Word.twoSteps D.word : ℤ) * (R.crossingLength : ℤ) =
          (Word.oddSteps D.word : ℤ) *
            (Word.prefixTwoDepth (D.cutRotation a) R.crossingLength : ℤ) := by
      linarith
    have hEqNat :
        Word.twoSteps D.word * R.crossingLength =
          Word.oddSteps D.word *
            Word.prefixTwoDepth (D.cutRotation a) R.crossingLength := by
      exact_mod_cast hEqZ
    have hDvd :
        Word.oddSteps D.word ∣
          Word.twoSteps D.word * R.crossingLength := by
      exact ⟨Word.prefixTwoDepth (D.cutRotation a) R.crossingLength,
        hEqNat⟩
    have hCop :
        Nat.Coprime (Word.oddSteps D.word) (Word.twoSteps D.word) := by
      simpa [Word.ContractingExponentPair.IsPrimitive,
        exponentPair_oddCount, exponentPair_twoDepth,
        Nat.coprime_comm] using hPrimitive
    have hDvdR : Word.oddSteps D.word ∣ R.crossingLength :=
      hCop.dvd_of_dvd_mul_left hDvd
    have hLeR : Word.oddSteps D.word ≤ R.crossingLength :=
      Nat.le_of_dvd R.crossingLength_pos hDvdR
    omega
  exact lt_of_le_of_ne hLe hNe

/-- strict descent endpoint の signed rank は nonnegative。 -/
theorem nextRank_nonneg
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    0 ≤ Word.chordRankInt D.word R.nextIndex := by
  have hF := D.wordFirstCrossing
  have hNextPos : 0 < R.nextIndex := by
    have hCrossPos : 0 < R.crossingLength :=
      R.crossingLength_pos
    unfold nextIndex
    omega
  exact hF.chordRankInt_nonneg_of_pos_le hNextPos R.next_le_terminal

/-- crossing block が作る signed rank difference の exact formula。 -/
theorem rankDifference_eq
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    Word.chordRankInt D.word R.nextIndex -
        Word.chordRankInt D.word a =
      (Word.twoSteps D.word : ℤ) * (R.crossingLength : ℤ) -
        (Word.oddSteps D.word : ℤ) *
          (Word.twoSteps R.block : ℤ) := by
  have hFormula :=
    D.cutRotation_rank_formula
      (a := a) R.crossingLength_le_suffix
  have hShift :=
    D.cutRotation_rank_shift
      (a := a)
      (r := R.crossingLength)
      R.crossingLength_le_suffix
  calc
    Word.chordRankInt D.word R.nextIndex -
          Word.chordRankInt D.word a
        = Word.chordRankInt (D.cutRotation a) R.crossingLength := by
            rw [hShift]
            rfl
    _ = (Word.twoSteps D.word : ℤ) * (R.crossingLength : ℤ) -
          (Word.oddSteps D.word : ℤ) *
            (Word.twoSteps R.block : ℤ) := by
            simpa [block] using hFormula

/--
primitive + reduced branch で start rank が `p` 未満なら crossing block は
最小 contracting depth `criticalHeight(r)+1` を持つ。
-/
theorem block_twoSteps_eq_critical_add_one
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (hStartLt : Word.chordRank D.word a < Word.oddSteps D.word) :
    Word.twoSteps R.block = Word.criticalHeight R.crossingLength + 1 := by
  have hF := D.wordFirstCrossing
  have haPos := R.cutIndex_pos
  have haLt := R.cutIndex_lt
  have hStartIntEq := hF.chordRankInt_eq_natCast haPos haLt
  have hStartLtZ :
      Word.chordRankInt D.word a < (Word.oddSteps D.word : ℤ) := by
    rw [hStartIntEq]
    exact_mod_cast hStartLt
  have hNextNonneg := R.nextRank_nonneg
  have hStrict :=
    R.crossingRank_strict_of_primitive_reduced hPrimitive hReduced
  have hBlockC : Word.Contracting R.block := by
    simpa [block] using R.firstCrossing.terminalContracting
  have hBlockLen : Word.oddSteps R.block = R.crossingLength := by
    unfold block Word.oddSteps
    exact List.length_take_of_le R.crossingLength_le_suffix
  have hBlockPowRaw :=
    (Word.contracting_iff_threePow_lt_twoPow).1 hBlockC
  have hBlockPowRaw :=
    (Word.contracting_iff_threePow_lt_twoPow).1 hBlockC
  have hBlockPow :
      3 ^ R.crossingLength < 2 ^ Word.twoSteps R.block := by
    rw [← hBlockLen]
    exact hBlockPowRaw
  have hLower :
      Word.criticalHeight R.crossingLength < Word.twoSteps R.block :=
    Word.criticalHeight_lt_of_threePow_lt_twoPow
      R.crossingLength_pos hBlockPow
  by_contra hnot
  have hDeltaGe :
      Word.criticalHeight R.crossingLength + 2 ≤
        Word.twoSteps R.block := by
    omega
  have hrLtWhole := R.crossingLength_lt_whole
  have hBest :=
    Word.ContractingExponentPair.bestUpper_of_stripReduced hReduced
      R.crossingLength R.crossingLength_pos hrLtWhole
  have hBestNat :
      Word.twoSteps D.word * R.crossingLength ≤
        Word.oddSteps D.word *
          (Word.criticalHeight R.crossingLength + 1) := by
    simpa using hBest
  have hBestZ :
      (Word.twoSteps D.word : ℤ) * (R.crossingLength : ℤ) ≤
        (Word.oddSteps D.word : ℤ) *
          (Word.criticalHeight R.crossingLength + 1 : ℤ) := by
    exact_mod_cast hBestNat
  have hDeltaScaled :
      Word.oddSteps D.word *
          (Word.criticalHeight R.crossingLength + 2) ≤
        Word.oddSteps D.word * Word.twoSteps R.block :=
    Nat.mul_le_mul_left (Word.oddSteps D.word) hDeltaGe
  have hDeltaScaledZ :
      (Word.oddSteps D.word : ℤ) *
          (Word.criticalHeight R.crossingLength + 2 : ℤ) ≤
        (Word.oddSteps D.word : ℤ) *
          (Word.twoSteps R.block : ℤ) := by
    exact_mod_cast hDeltaScaled
  have hRankEquation := R.rankDifference_eq
  nlinarith [hStrict]

/--
minimal block では rank drop は exact に `p - stripRank(r)`。
後の record chain telescope 用の整数形。
-/
theorem rankDrop_eq_oddSteps_sub_stripRank
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (hStartLt : Word.chordRank D.word a < Word.oddSteps D.word) :
    Word.chordRankInt D.word a -
        Word.chordRankInt D.word R.nextIndex =
      (Word.oddSteps D.word : ℤ) -
        (Word.stripRank D.word R.crossingLength : ℤ) := by
  have hDepth :=
    R.block_twoSteps_eq_critical_add_one
      hPrimitive hReduced hStartLt
  have hDiff := R.rankDifference_eq
  have hCrit :=
    D.exponentPair.criticalHeight_below_chord R.crossingLength_pos
  have hCritWord :
      Word.oddSteps D.word * Word.criticalHeight R.crossingLength <
        Word.twoSteps D.word * R.crossingLength := by
    simpa using hCrit
  have hStripCast :
      (Word.stripRank D.word R.crossingLength : ℤ) =
        (Word.twoSteps D.word : ℤ) * (R.crossingLength : ℤ) -
          (Word.oddSteps D.word : ℤ) *
            (Word.criticalHeight R.crossingLength : ℤ) := by
    unfold Word.stripRank
    rw [Nat.cast_sub (Nat.le_of_lt hCritWord)]
    push_cast
    ring
  have hDepthZ :
      (Word.twoSteps R.block : ℤ) =
        (Word.criticalHeight R.crossingLength : ℤ) + 1 := by
    exact_mod_cast hDepth
  rw [hDepthZ] at hDiff
  rw [hStripCast]
  linarith

/-- start rank が `p` 未満ならその cut は critical roof 上。 -/
theorem prefixTwoDepth_eq_criticalHeight_of_rank_lt
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (haPos : 0 < a)
    (haLt : a < Word.oddSteps D.word)
    (hRankLt : Word.chordRank D.word a < Word.oddSteps D.word) :
    Word.prefixTwoDepth D.word a = Word.criticalHeight a := by
  have hF := D.wordFirstCrossing
  have hDecomp :=
    hF.chordRank_eq_stripRank_add_extraDepth haPos haLt
  have hExtraZero : Word.extraDepth D.word a = 0 := by
    by_contra hne
    have hExtraPos : 0 < Word.extraDepth D.word a := by omega
    have hpPos : 0 < Word.oddSteps D.word :=
      D.exponentPair.oddCount_pos
    have hpLe :
        Word.oddSteps D.word ≤
          Word.oddSteps D.word * Word.extraDepth D.word a := by
      calc
        Word.oddSteps D.word
            = Word.oddSteps D.word * 1 := by ring
        _ ≤ Word.oddSteps D.word * Word.extraDepth D.word a :=
          Nat.mul_le_mul_left _ (by omega)
    have hRankGe :
        Word.oddSteps D.word ≤ Word.chordRank D.word a := by
      omega
    omega
  unfold Word.extraDepth at hExtraZero
  have hLe := hF.prefixTwoDepth_le_criticalHeight haPos haLt
  omega

/-- interior next record も critical roof 上に乗る。 -/
theorem next_prefixTwoDepth_eq_criticalHeight_of_interior
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (hStartLt : Word.chordRank D.word a < Word.oddSteps D.word)
    (hInterior : R.nextIndex < Word.oddSteps D.word) :
    Word.prefixTwoDepth D.word R.nextIndex =
      Word.criticalHeight R.nextIndex := by
  have hF := D.wordFirstCrossing
  have hStrict :=
    R.crossingRank_strict_of_primitive_reduced hPrimitive hReduced
  have hStartIntEq :=
    hF.chordRankInt_eq_natCast R.cutIndex_pos R.cutIndex_lt
  have hNextPos : 0 < R.nextIndex := by
    have hCrossPos : 0 < R.crossingLength :=
      R.crossingLength_pos
    unfold nextIndex
    omega
  have hNextIntEq :=
    hF.chordRankInt_eq_natCast hNextPos hInterior
  have hNextLt :
      Word.chordRank D.word R.nextIndex < Word.oddSteps D.word := by
    rw [hStartIntEq, hNextIntEq] at hStrict
    have hNatStrict :
        Word.chordRank D.word R.nextIndex < Word.chordRank D.word a := by
      exact_mod_cast hStrict
    exact lt_trans hNatStrict hStartLt
  exact prefixTwoDepth_eq_criticalHeight_of_rank_lt
    hNextPos hInterior hNextLt

end CutRecordTrapData

/--
one-step record block packet。これを nextIndex へ反復できる。
-/
structure NextRecordBlockData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (startIndex : ℕ) where
  trap : CutRecordTrapData D startIndex
  start_roof :
    Word.prefixTwoDepth D.word startIndex =
      Word.criticalHeight startIndex
  rank_strict :
    Word.chordRankInt D.word trap.nextIndex <
      Word.chordRankInt D.word startIndex
  block_minimal_depth :
    Word.twoSteps trap.block =
      Word.criticalHeight trap.crossingLength + 1
  rank_drop_exact :
    Word.chordRankInt D.word startIndex -
        Word.chordRankInt D.word trap.nextIndex =
      (Word.oddSteps D.word : ℤ) -
        (Word.stripRank D.word trap.crossingLength : ℤ)
  next_roof_if_interior :
    trap.nextIndex < Word.oddSteps D.word →
      Word.prefixTwoDepth D.word trap.nextIndex =
        Word.criticalHeight trap.nextIndex

/--
Stage 3b: primitive + reduced branch の任意 `0<d_a<p` record から次 block を構成する。
-/
noncomputable def exists_nextRecordBlock
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (a : ℕ)
    (haPos : 0 < a)
    (haLt : a < Word.oddSteps D.word)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (hRankLt : Word.chordRank D.word a < Word.oddSteps D.word) :
    NextRecordBlockData D a := by
  classical
  let R := D.toCutRecordTrapData a haPos haLt
  exact {
    trap := R
    start_roof :=
      CutRecordTrapData.prefixTwoDepth_eq_criticalHeight_of_rank_lt haPos haLt hRankLt
    rank_strict :=
      R.crossingRank_strict_of_primitive_reduced hPrimitive hReduced
    block_minimal_depth :=
      R.block_twoSteps_eq_critical_add_one hPrimitive hReduced hRankLt
    rank_drop_exact :=
      R.rankDrop_eq_oddSteps_sub_stripRank hPrimitive hReduced hRankLt
    next_roof_if_interior := fun hInterior =>
      R.next_prefixTwoDepth_eq_criticalHeight_of_interior
        hPrimitive hReduced hRankLt hInterior
  }

/-! ## current A の初期 record `a=1` -/

/-- current A では first prefix depth は1。 -/
theorem prefixTwoDepth_one_eq_one
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.prefixTwoDepth D.word 1 = 1 := by
  let N := D.toNaturalCoordinates
  rw [N.word_eq]
  simp [Word.prefixTwoDepth, Word.twoSteps]

/-- critical height at one。 -/
@[simp] theorem criticalHeight_one : Word.criticalHeight 1 = 1 := by
  decide

/-- primitive+reduced branch では初期 rank `d_1` は `0<d_1<p`。 -/
theorem firstRank_pos_lt_of_primitive_reduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    0 < Word.chordRank D.word 1 ∧
      Word.chordRank D.word 1 < Word.oddSteps D.word := by
  have hLen : 1 < Word.oddSteps D.word := by
    simpa [Word.oddSteps] using D.word_length_gt_one
  have hF := D.wordFirstCrossing
  have hPos := hF.chordRank_pos (by omega) hLen
  have hExtra : Word.extraDepth D.word 1 = 0 := by
    unfold Word.extraDepth
    rw [D.prefixTwoDepth_one_eq_one, criticalHeight_one]
  have hDecomp :=
    hF.chordRank_eq_stripRank_add_extraDepth (by omega) hLen
  rw [hExtra, mul_zero, add_zero] at hDecomp
  have hLenPair : 1 < D.exponentPair.oddCount := by
    simpa using hLen
  have hLePair := hReduced 1 (by omega) hLenPair
  have hLeWord :
      Word.stripRank D.word 1 ≤ Word.oddSteps D.word := by
    simpa [D.exponentPair_stripRank_eq] using hLePair
  have hNe :=
    D.exponentPair.stripRank_ne_oddCount_of_primitive
      hPrimitive (by omega) hLenPair
  have hNeWord : Word.stripRank D.word 1 ≠ Word.oddSteps D.word := by
    simpa [D.exponentPair_stripRank_eq] using hNe
  constructor
  · exact hPos
  · rw [hDecomp]
    exact lt_of_le_of_ne hLeWord hNeWord

/-- primitive+reduced branch の initial record block。 -/
noncomputable def initialNextRecordBlock
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    NextRecordBlockData D 1 := by
  have hRange := D.firstRank_pos_lt_of_primitive_reduced hPrimitive hReduced
  have hLen : 1 < Word.oddSteps D.word := by
    simpa [Word.oddSteps] using D.word_length_gt_one
  exact D.exists_nextRecordBlock
    1 (by omega) hLen hPrimitive hReduced hRange.2

/-- first rank は exact に `H-p`。 -/
theorem firstRank_eq_twoDepth_sub_oddCount
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.chordRank D.word 1 =
      Word.twoSteps D.word - Word.oddSteps D.word := by
  unfold Word.chordRank
  rw [D.prefixTwoDepth_one_eq_one]
  simp

/-- 初等 slope bound から `12*d_1 > 7*p`。 -/
theorem seven_mul_oddSteps_lt_twelve_mul_firstRank
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    7 * Word.oddSteps D.word <
      12 * Word.chordRank D.word 1 := by
  have hSlope :=
    Word.nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
      D.exponentPair.oddCount_pos
      D.exponentPair.contracting
  have hSlope' :
      19 * Word.oddSteps D.word < 12 * Word.twoSteps D.word := by
    simpa using hSlope
  have hRankEq := D.firstRank_eq_twoDepth_sub_oddCount
  have hpPos : 0 < Word.oddSteps D.word :=
    D.exponentPair.oddCount_pos
  rw [hRankEq]
  omega

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
