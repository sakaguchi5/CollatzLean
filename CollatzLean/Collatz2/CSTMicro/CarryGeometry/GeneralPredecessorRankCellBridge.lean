import CollatzLean.Collatz2.CSTMicro.CarryGeometry.BoundaryRespectingRankCellBridge

/-!
# General predecessor Ferrers cell -> odd-only rank cell

`BoundaryRespectingRankCellBridge` で selected cell に対して得た

  3 * cellCost = inverseRankWeight(t)  (mod G)

を、selected packet から外して一般の adjacent Ferrers cell へ持ち上げる。
upper parity word が first-passage なら、その odd-only run encoding は FirstCrossing であり、
cell cut

  t = oddCount(leftContext)

に対して

  prefixTwoDepth(t) = position,
  normalizedCutTerm(t) = 3 * deltaB

が exact に成り立つ。これと full-scale cell-cost identity を組み合わせる。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. standard first-passage -> odd-only FirstCrossing, generally -/

namespace IsFirstPassageWord

/-- length > 1 の first-passage parity word は leading even-run を持たない。 -/
theorem leadingEvenCount_eq_zero_of_one_lt_length
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    leadingEvenCount v = 0 := by
  obtain ⟨t, ht⟩ := h.exists_eq_true_cons hlen
  rw [ht]
  simp

/-- leading run が zero なので odd-only exponent sum は standard length そのもの。 -/
@[simp] theorem twoSteps_exponentWordOfParity_eq_length
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    Collatz2.Word.twoSteps (exponentWordOfParity v) = v.length := by
  have hLen := leadingEvenCount_add_twoSteps_exponentWordOfParity v
  rw [h.leadingEvenCount_eq_zero_of_one_lt_length hlen, zero_add] at hLen
  exact hLen

/-- standard first-passage の proper expansion は odd-only run checkpoint 全体へ降りる。 -/
theorem exponentWordOfParity_properPositive
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    Collatz2.Word.ProperPrefixesPositiveDeterminant
      (exponentWordOfParity v) := by
  intro k hkPos hkLt
  let w := exponentWordOfParity v
  have hvalid : Collatz2.Word.Valid w := by
    simpa [w] using exponentWordOfParity_valid v
  have hkLtOdd : k < Collatz2.Word.oddSteps w := by
    simpa [Collatz2.Word.oddSteps] using hkLt
  have hkLe : k ≤ Collatz2.Word.oddSteps w := Nat.le_of_lt hkLtOdd
  have hCountRaw :=
    prefixOddCount_at_exponent_checkpoint
      v k (by simpa [w] using hkLe)
  have hCount :
      prefixOddCount v (Collatz2.Word.twoSteps (w.take k)) = k := by
    rw [h.leadingEvenCount_eq_zero_of_one_lt_length hlen, zero_add] at hCountRaw
    simpa [w] using hCountRaw
  have htakeValid : Collatz2.Word.Valid (w.take k) := by
    have hwhole : Collatz2.Word.Valid (w.take k ++ w.drop k) := by
      simpa using hvalid
    exact hwhole.prefix
  have htakeNonempty : w.take k ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hkLen : k ≤ w.length := by
      simpa [Collatz2.Word.oddSteps] using hkLe
    rw [List.length_take_of_le hkLen]
    exact hkPos
  have htimePos : 0 < Collatz2.Word.twoSteps (w.take k) :=
    Collatz2.Word.twoSteps_pos_of_valid_nonempty htakeValid htakeNonempty
  have htimeLtWord :
      Collatz2.Word.twoSteps (w.take k) < Collatz2.Word.twoSteps w :=
    twoSteps_take_lt_of_valid hvalid hkLtOdd
  have htimeLt :
      Collatz2.Word.twoSteps (w.take k) < v.length := by
    calc
      Collatz2.Word.twoSteps (w.take k)
          < Collatz2.Word.twoSteps w := htimeLtWord
      _ = v.length := by
        simpa [w] using h.twoSteps_exponentWordOfParity_eq_length hlen
  have hExp := h.2.1
    (Collatz2.Word.twoSteps (w.take k)) htimePos htimeLt
  unfold CoefficientExpandingAt at hExp
  rw [hCount] at hExp
  change Collatz2.Word.Expanding (w.take k)
  apply (Collatz2.Word.expanding_iff_twoPow_lt_threePow).2
  have hkLen : k ≤ w.length := by
    simpa [Collatz2.Word.oddSteps] using hkLe
  have hOddTake : Collatz2.Word.oddSteps (w.take k) = k := by
    unfold Collatz2.Word.oddSteps
    exact List.length_take_of_le hkLen
  simpa [hOddTake] using hExp

/-- standard terminal contraction は odd-only run encoding の terminal contraction。 -/
theorem exponentWordOfParity_terminalContracting
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    Collatz2.Word.Contracting (exponentWordOfParity v) := by
  apply (Collatz2.Word.contracting_iff_threePow_lt_twoPow).2
  have hContract := h.2.2
  unfold CoefficientContracting at hContract
  rw [oddSteps_exponentWordOfParity]
  rw [h.twoSteps_exponentWordOfParity_eq_length hlen]
  exact hContract

/-- standard first-passage parity word の odd-only run encoding は FirstCrossing。 -/
theorem exponentWordOfParity_firstCrossing
    {v : ParityWord}
    (h : IsFirstPassageWord v)
    (hlen : 1 < v.length) :
    Collatz2.Word.FirstCrossing (exponentWordOfParity v) := by
  have hNonempty : exponentWordOfParity v ≠ [] := by
    obtain ⟨t, ht⟩ := h.exists_eq_true_cons hlen
    rw [ht]
    simp
  exact {
    nonempty := hNonempty
    properPositive := h.exponentWordOfParity_properPositive hlen
    terminalNegative := h.exponentWordOfParity_terminalContracting hlen
  }

end IsFirstPassageWord

/-! ## 2. arbitrary adjacent upper cell -> rank cut -/

namespace AdjacentFerrersSwap

/-- adjacent cell に対応する odd-only cut。 -/
def rankCut (S : AdjacentFerrersSwap) : ℕ :=
  oddCount S.leftContext

/-- upper parity word の odd-only run encoding。 -/
def rankUpperExponentWord (S : AdjacentFerrersSwap) : Collatz2.Word :=
  exponentWordOfParity S.upperWord

/-- adjacent upper word は構造上 length >= 2。 -/
theorem one_lt_rankUpperWord_length (S : AdjacentFerrersSwap) :
    1 < S.upperWord.length := by
  rw [S.upperWord_length]
  unfold AdjacentFerrersSwap.length
  omega

/-- encoded upper の odd step 数は common odd total。 -/
@[simp] theorem rankUpperExponentWord_oddSteps
    (S : AdjacentFerrersSwap) :
    Collatz2.Word.oddSteps S.rankUpperExponentWord = S.oddTotal := by
  unfold rankUpperExponentWord
  rw [oddSteps_exponentWordOfParity]
  exact S.upperWord_oddCount

/-- upper first-passage なら encoded total two-depth は common length。 -/
@[simp] theorem rankUpperExponentWord_twoSteps
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.twoSteps S.rankUpperExponentWord = S.length := by
  unfold rankUpperExponentWord
  calc
    Collatz2.Word.twoSteps (exponentWordOfParity S.upperWord)
        = S.upperWord.length :=
      hUpperFP.twoSteps_exponentWordOfParity_eq_length S.one_lt_rankUpperWord_length
    _ = S.length := S.upperWord_length

/-- upper first-passage なら encoded upper は FirstCrossing。 -/
theorem rankUpperExponentWord_firstCrossing
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.FirstCrossing S.rankUpperExponentWord := by
  unfold rankUpperExponentWord
  exact hUpperFP.exponentWordOfParity_firstCrossing S.one_lt_rankUpperWord_length

/-- selected adjacent cut は常に proper。 -/
theorem rankCut_lt_oddSteps
    (S : AdjacentFerrersSwap) :
    S.rankCut < Collatz2.Word.oddSteps S.rankUpperExponentWord := by
  rw [S.rankUpperExponentWord_oddSteps]
  unfold rankCut AdjacentFerrersSwap.oddTotal
  omega

/-- upper first-passage なら leading even-run は zero。 -/
theorem rankUpper_leadingEvenCount_eq_zero
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    leadingEvenCount S.upperWord = 0 :=
  hUpperFP.leadingEvenCount_eq_zero_of_one_lt_length S.one_lt_rankUpperWord_length

/--
upper `10` cell の odd cut checkpoint は exact に swap position。
-/
theorem prefixTwoDepth_rankCut_eq_position
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.prefixTwoDepth S.rankUpperExponentWord S.rankCut =
      S.position := by
  have hRun :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
      S.leftContext
      (false :: S.rightContext)
  change
    leadingEvenCount S.upperWord +
        Collatz2.Word.twoSteps
          ((exponentWordOfParity S.upperWord).take
            (oddCount S.leftContext)) =
      S.leftContext.length at hRun
  rw [S.rankUpper_leadingEvenCount_eq_zero hUpperFP, zero_add] at hRun
  unfold Collatz2.Word.prefixTwoDepth rankUpperExponentWord rankCut
  unfold AdjacentFerrersSwap.position
  exact hRun

/-- selected normalized cut term は exact に `3 * deltaB`。 -/
theorem normalizedCutTerm_rankCut_eq_three_mul_deltaB
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.normalizedCutTerm S.rankUpperExponentWord S.rankCut =
      3 * S.deltaB := by
  have hSub :
      S.oddTotal - S.rankCut = oddCount S.rightContext + 1 := by
    unfold AdjacentFerrersSwap.oddTotal rankCut
    omega
  unfold Collatz2.Word.normalizedCutTerm
  rw [S.prefixTwoDepth_rankCut_eq_position hUpperFP]
  rw [S.rankUpperExponentWord_oddSteps, hSub]
  unfold AdjacentFerrersSwap.deltaB
  rw [pow_succ]
  ring

/-- encoded upper terminal gap の integer cast は local Farey `G`。 -/
theorem rankUpper_terminalGap_cast_eq_fareyG
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    (Collatz2.Word.terminalGap S.rankUpperExponentWord : ℤ) =
      S.toFareyCellPacket.G := by
  have hF := S.rankUpperExponentWord_firstCrossing hUpperFP
  have hContract :
      3 ^ Collatz2.Word.oddSteps S.rankUpperExponentWord <
        2 ^ Collatz2.Word.twoSteps S.rankUpperExponentWord :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
  unfold Collatz2.Word.terminalGap
  rw [Nat.cast_sub (Nat.le_of_lt hContract)]
  rw [S.rankUpperExponentWord_twoSteps hUpperFP]
  rw [S.rankUpperExponentWord_oddSteps]
  change
    (2 : ℤ) ^ S.length - (3 : ℤ) ^ S.oddTotal =
      S.toFareyCellPacket.G
  rfl

/-- mod terminal gap では `2^H = 3^p`。 -/
theorem rankUpper_twoPow_cast_eq_threePow_cast
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    (((2 ^ Collatz2.Word.twoSteps S.rankUpperExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) =
      (((3 ^ Collatz2.Word.oddSteps S.rankUpperExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) := by
  let w := S.rankUpperExponentWord
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using S.rankUpperExponentWord_firstCrossing hUpperFP
  have hPow :
      3 ^ Collatz2.Word.oddSteps w < 2 ^ Collatz2.Word.twoSteps w :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
  have hAdd :
      Collatz2.Word.terminalGap w + 3 ^ Collatz2.Word.oddSteps w =
        2 ^ Collatz2.Word.twoSteps w := by
    unfold Collatz2.Word.terminalGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hCast :=
    congrArg
      (fun n : ℕ => (n : ZMod (Collatz2.Word.terminalGap w)))
      hAdd
  have hGapZero :
      ((Collatz2.Word.terminalGap w : ℕ) :
        ZMod (Collatz2.Word.terminalGap w)) = 0 := by
    exact ZMod.natCast_self _
  simp only [Nat.cast_add] at hCast
  rw [hGapZero, zero_add] at hCast
  simpa [w] using hCast.symm

/--
任意 adjacent upper first-passage cell の rank bridge。

  3 * fareyCellCost = inverseRankWeight(rankCut)  (mod G).
-/
theorem three_mul_fareyCellCost_cast_eq_inverseRankWeight
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord)
    (R : Collatz2.Word.RankUnitData S.rankUpperExponentWord) :
    ((3 : ℤ) : ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) *
        (S.fareyCellCost : ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) =
      Collatz2.Word.inverseRankWeight R S.rankCut := by
  let w := S.rankUpperExponentWord
  let G := Collatz2.Word.terminalGap w
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using S.rankUpperExponentWord_firstCrossing hUpperFP
  have hFull := S.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
  have hGapInt : S.toFareyCellPacket.G = (G : ℤ) := by
    dsimp [G, w]
    exact (S.rankUpper_terminalGap_cast_eq_fareyG hUpperFP).symm
  have hCast := congrArg (fun z : ℤ => (z : ZMod G)) hFull
  push_cast at hCast
  have hGapZero :
      ((S.toFareyCellPacket.G : ℤ) : ZMod G) = 0 := by
    rw [hGapInt]
    simp
  rw [hGapZero, zero_mul, zero_add] at hCast
  have hLength : S.length = Collatz2.Word.twoSteps w := by
    simpa [w] using (S.rankUpperExponentWord_twoSteps hUpperFP).symm
  rw [hLength] at hCast
  have hCastNat :
      (((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
          (S.fareyCellCost : ZMod G) =
        ((S.deltaB : ℕ) : ZMod G) := by
    push_cast
    exact hCast
  have hPow :
      (((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) := by
    simpa [w] using S.rankUpper_twoPow_cast_eq_threePow_cast hUpperFP
  have hTermNat := S.normalizedCutTerm_rankCut_eq_three_mul_deltaB hUpperFP
  have hTermCast :
      ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) =
        (((3 * S.deltaB : ℕ)) : ZMod G) := by
    exact congrArg (fun n : ℕ => (n : ZMod G)) hTermNat
  have hScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          (((3 : ℤ) : ZMod G) * (S.fareyCellCost : ZMod G)) =
        ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) := by
    calc
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
            (((3 : ℤ) : ZMod G) * (S.fareyCellCost : ZMod G))
          =
        (((3 : ℤ) : ZMod G) *
          ((((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
            (S.fareyCellCost : ZMod G))) := by
              rw [hPow]
              ring
      _ =
        (((3 : ℤ) : ZMod G) * ((S.deltaB : ℕ) : ZMod G)) := by
          rw [hCastNat]
      _ = (((3 * S.deltaB : ℕ)) : ZMod G) := by
          push_cast
          ring
      _ = ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) :=
          hTermCast.symm
  have hCert :=
    R.normalizedCutTerm_eq_threePow_mul_inverseRankWeight
      hF S.rankCut_lt_oddSteps
  have hEq :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          (((3 : ℤ) : ZMod G) * (S.fareyCellCost : ZMod G)) =
        (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          Collatz2.Word.inverseRankWeight R S.rankCut := by
    exact hScaled.trans hCert
  exact R.cancel_threePow hEq

end AdjacentFerrersSwap

end CSTMicro
end Collatz2
