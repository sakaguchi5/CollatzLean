import CollatzLean.Collatz2.CSTMicro.CarryGeometry.LocalRankTopLedger

set_option linter.style.longLine false

/-!
# Universal rank-top transport across one Ferrers step

`UniversalCutWeight` により primitive 条件なしで各 odd-only cut に top weight を置ける。
このファイルでは adjacent Ferrers move `01 -> 10` に対して

* selected cut の upper top は `3*C mod G`,
* selected cut の lower top は `6*C mod G`,
* selected cut 以外の top representative は不変

を証明する。

核心は run encoder の checkpoint

  leadingEvenCount(v) + twoSteps((exponentWordOfParity v).take k)

である。`01 -> 10` は `k = oddCount(leftContext)` の checkpoint だけを 1 左へ動かし、
他の checkpoint は exact に保存する。
-/

namespace Collatz2
namespace CSTMicro

/-- parity run encoder の standard-time checkpoint。 -/
def exponentCheckpoint (v : ParityWord) (k : ℕ) : ℕ :=
  leadingEvenCount v +
    Collatz2.Word.twoSteps ((exponentWordOfParity v).take k)

/-- 先頭 even は全 checkpoint を standard time で 1 だけ右へずらす。 -/
@[simp] theorem exponentCheckpoint_false_cons
    (v : ParityWord)
    (k : ℕ) :
    exponentCheckpoint (false :: v) k =
      exponentCheckpoint v k + 1 := by
  unfold exponentCheckpoint
  simp only [
    leadingEvenCount_false_cons,
    exponentWordOfParity_false_cons
  ]
  omega


/-- 先頭 odd の zero-th checkpoint は時刻 0。 -/
@[simp] theorem exponentCheckpoint_true_cons_zero
    (v : ParityWord) :
    exponentCheckpoint (true :: v) 0 = 0 := by
  simp [exponentCheckpoint]


/--
先頭 odd を1 run 消費した後の checkpoint は、
tail の対応 checkpoint より standard time で 1 だけ後。
-/
@[simp] theorem exponentCheckpoint_true_cons_succ
    (v : ParityWord)
    (k : ℕ) :
    exponentCheckpoint (true :: v) (k + 1) =
      exponentCheckpoint v k + 1 := by
  unfold exponentCheckpoint
  simp only [
    leadingEvenCount_true_cons,
    exponentWordOfParity_true_cons,
    List.take_succ_cons,
    Collatz2.Word.twoSteps_cons,
    zero_add
  ]
  omega

/--
`p ++ 01 ++ rest -> p ++ 10 ++ rest` では selected odd cut 以外の
run checkpoint は exact に不変。

leading even-run を checkpoint に含めることで `p=[]` の場合も一様に成立する。
-/
theorem exponentCheckpoint_swap_eq_of_ne_leftOdd
    (p rest : ParityWord)
    (k : ℕ)
    (hk : k ≠ oddCount p) :
    exponentCheckpoint (p ++ true :: false :: rest) k =
      exponentCheckpoint (p ++ false :: true :: rest) k := by
  induction p generalizing k with
  | nil =>
      have hk0 : k ≠ 0 := by
        simpa [oddCount] using hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      simp [Nat.succ_eq_add_one]
  | cons b p ih =>
      cases b with
      | false =>
          have hk' : k ≠ oddCount p := by
            simpa using hk
          have hih := ih (k := k) hk'
          simp only [
            List.cons_append,
            exponentCheckpoint_false_cons
          ]
          exact congrArg (fun n : ℕ => n + 1) hih
      | true =>
          by_cases hk0 : k = 0
          · subst k
            simp
          · obtain ⟨j, rfl⟩ :=
              Nat.exists_eq_succ_of_ne_zero hk0
            have hj : j ≠ oddCount p := by
              intro hEq
              apply hk
              simp [oddCount_true_cons, hEq]
            have hih := ih (k := j) hj
            simp only [
              List.cons_append,
              exponentCheckpoint_true_cons_succ,
              Nat.succ_eq_add_one
            ]
            exact congrArg (fun n : ℕ => n + 1) hih

namespace AdjacentFerrersSwap

/-- encoded lower / upper は lower first-passage の下で同じ terminal gap を持つ。 -/
theorem rankLower_terminalGap_eq_rankUpper_terminalGap
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.terminalGap S.rankLowerExponentWord =
      Collatz2.Word.terminalGap S.rankUpperExponentWord := by
  unfold Collatz2.Word.terminalGap
  rw [S.rankLowerExponentWord_twoSteps hLowerFP]
  rw [S.rankUpperExponentWord_twoSteps hUpperFP]
  rw [S.rankLowerExponentWord_oddSteps]
  rw [S.rankUpperExponentWord_oddSteps]

/-- lower encoded terminal gap の integer cast も local Farey `G`。 -/
theorem rankLower_terminalGap_cast_eq_fareyG
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    (Collatz2.Word.terminalGap S.rankLowerExponentWord : ℤ) =
      S.toFareyCellPacket.G := by
  have hF := S.rankLowerExponentWord_firstCrossing hLowerFP
  have hContract :
      3 ^ Collatz2.Word.oddSteps S.rankLowerExponentWord <
        2 ^ Collatz2.Word.twoSteps S.rankLowerExponentWord :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
  unfold Collatz2.Word.terminalGap
  rw [Nat.cast_sub (Nat.le_of_lt hContract)]
  rw [S.rankLowerExponentWord_twoSteps hLowerFP]
  rw [S.rankLowerExponentWord_oddSteps]
  change
    (2 : ℤ) ^ S.length - (3 : ℤ) ^ S.oddTotal =
      S.toFareyCellPacket.G
  rfl

/-- lower encoded modulus でも `2^H = 3^p`。 -/
theorem rankLower_twoPow_cast_eq_threePow_cast
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    (((2 ^ Collatz2.Word.twoSteps S.rankLowerExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap S.rankLowerExponentWord)) =
      (((3 ^ Collatz2.Word.oddSteps S.rankLowerExponentWord : ℕ)) :
        ZMod (Collatz2.Word.terminalGap S.rankLowerExponentWord)) := by
  let w := S.rankLowerExponentWord
  have hF : Collatz2.Word.FirstCrossing w := by
    simpa [w] using S.rankLowerExponentWord_firstCrossing hLowerFP
  have hPow :
      3 ^ Collatz2.Word.oddSteps w < 2 ^ Collatz2.Word.twoSteps w :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
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
        ZMod (Collatz2.Word.terminalGap w)) = 0 :=
    ZMod.natCast_self _
  simp only [Nat.cast_add] at hCast
  rw [hGapZero, zero_add] at hCast
  simpa [w] using hCast.symm

/-- lower selected normalized cut term は exact に `6 * deltaB`。 -/
theorem rankLower_normalizedCutTerm_rankCut_eq_six_mul_deltaB
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.normalizedCutTerm S.rankLowerExponentWord S.rankCut =
      6 * S.deltaB := by
  have hSub :
      S.oddTotal - S.rankCut = oddCount S.rightContext + 1 := by
    unfold AdjacentFerrersSwap.oddTotal rankCut
    omega
  unfold Collatz2.Word.normalizedCutTerm
  rw [S.prefixTwoDepth_rankCut_eq_position_add_one hLowerFP]
  rw [S.rankLowerExponentWord_oddSteps, hSub]
  unfold AdjacentFerrersSwap.deltaB
  rw [pow_succ, pow_succ]
  ring

/--
upper selected cut の universal weight は primitive 条件なしで `3*C`。
-/
theorem universalCutWeight_rankCut_eq_three_mul_fareyCellCost
    (S : AdjacentFerrersSwap)
    (hUpperFP : IsFirstPassageWord S.upperWord) :
    Collatz2.Word.universalCutWeight
        (S.rankUpperExponentWord_firstCrossing hUpperFP) S.rankCut =
      (3 : ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) *
        (S.fareyCellCost :
          ZMod (Collatz2.Word.terminalGap S.rankUpperExponentWord)) := by
  let w := S.rankUpperExponentWord
  let G := Collatz2.Word.terminalGap w
  let hF : Collatz2.Word.FirstCrossing w :=
    S.rankUpperExponentWord_firstCrossing hUpperFP
  have hFull :=
    S.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
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
  have hTermNat :=
    S.normalizedCutTerm_rankCut_eq_three_mul_deltaB hUpperFP
  have hTermCast :
      ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) =
        (((3 * S.deltaB : ℕ)) : ZMod G) :=
    congrArg (fun n : ℕ => (n : ZMod G)) hTermNat
  have hScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          ((3 : ZMod G) * (S.fareyCellCost : ZMod G)) =
        ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) := by
    calc
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
            ((3 : ZMod G) * (S.fareyCellCost : ZMod G))
          =
        (3 : ZMod G) *
          ((((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
            (S.fareyCellCost : ZMod G)) := by
              rw [hPow]
              ring
      _ = (3 : ZMod G) * ((S.deltaB : ℕ) : ZMod G) := by
            rw [hCastNat]
      _ = (((3 * S.deltaB : ℕ)) : ZMod G) := by
            push_cast
            ring
      _ = ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) :=
            hTermCast.symm
  have hUniversal := hF.threePow_mul_universalCutWeight S.rankCut
  apply hF.cancel_threePow
  exact hUniversal.trans hScaled.symm

/--
lower selected cut の universal weight は primitive 条件なしで `6*C`。
-/
theorem rankLower_universalCutWeight_rankCut_eq_six_mul_fareyCellCost
    (S : AdjacentFerrersSwap)
    (hLowerFP : IsFirstPassageWord S.lowerWord) :
    Collatz2.Word.universalCutWeight
        (S.rankLowerExponentWord_firstCrossing hLowerFP) S.rankCut =
      (6 : ZMod (Collatz2.Word.terminalGap S.rankLowerExponentWord)) *
        (S.fareyCellCost :
          ZMod (Collatz2.Word.terminalGap S.rankLowerExponentWord)) := by
  let w := S.rankLowerExponentWord
  let G := Collatz2.Word.terminalGap w
  let hF : Collatz2.Word.FirstCrossing w :=
    S.rankLowerExponentWord_firstCrossing hLowerFP
  have hFull :=
    S.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
  have hGapInt : S.toFareyCellPacket.G = (G : ℤ) := by
    dsimp [G, w]
    exact (S.rankLower_terminalGap_cast_eq_fareyG hLowerFP).symm
  have hCast := congrArg (fun z : ℤ => (z : ZMod G)) hFull
  push_cast at hCast
  have hGapZero :
      ((S.toFareyCellPacket.G : ℤ) : ZMod G) = 0 := by
    rw [hGapInt]
    simp
  rw [hGapZero, zero_mul, zero_add] at hCast
  have hLength : S.length = Collatz2.Word.twoSteps w := by
    simpa [w] using (S.rankLowerExponentWord_twoSteps hLowerFP).symm
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
    simpa [w] using S.rankLower_twoPow_cast_eq_threePow_cast hLowerFP
  have hTermNat :=
    S.rankLower_normalizedCutTerm_rankCut_eq_six_mul_deltaB hLowerFP
  have hTermCast :
      ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) =
        (((6 * S.deltaB : ℕ)) : ZMod G) :=
    congrArg (fun n : ℕ => (n : ZMod G)) hTermNat
  have hScaled :
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
          ((6 : ZMod G) * (S.fareyCellCost : ZMod G)) =
        ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) := by
    calc
      (((3 ^ Collatz2.Word.oddSteps w : ℕ)) : ZMod G) *
            ((6 : ZMod G) * (S.fareyCellCost : ZMod G))
          =
        (6 : ZMod G) *
          ((((2 ^ Collatz2.Word.twoSteps w : ℕ)) : ZMod G) *
            (S.fareyCellCost : ZMod G)) := by
              rw [hPow]
              ring
      _ = (6 : ZMod G) * ((S.deltaB : ℕ) : ZMod G) := by
            rw [hCastNat]
      _ = (((6 * S.deltaB : ℕ)) : ZMod G) := by
            push_cast
            ring
      _ = ((Collatz2.Word.normalizedCutTerm w S.rankCut : ℕ) : ZMod G) :=
            hTermCast.symm
  have hUniversal := hF.threePow_mul_universalCutWeight S.rankCut
  apply hF.cancel_threePow
  exact hUniversal.trans hScaled.symm

end AdjacentFerrersSwap

namespace FerrersStep

/-- selected 以外の encoded checkpoint は lower/upper で不変。 -/
theorem prefixTwoDepth_rankUpper_eq_rankLower_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    Collatz2.Word.prefixTwoDepth S.edge.rankUpperExponentWord k =
      Collatz2.Word.prefixTwoDepth S.edge.rankLowerExponentWord k := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  have hCheckpoint :=
    exponentCheckpoint_swap_eq_of_ne_leftOdd
      S.edge.leftContext S.edge.rightContext k
      (by simpa [AdjacentFerrersSwap.rankCut] using hk)
  change
    exponentCheckpoint S.edge.upperWord k =
      exponentCheckpoint S.edge.lowerWord k at hCheckpoint
  unfold exponentCheckpoint at hCheckpoint
  rw [S.edge.rankUpper_leadingEvenCount_eq_zero hEdgeUpperFP,
      S.edge.rankLower_leadingEvenCount_eq_zero hEdgeLowerFP,
      zero_add, zero_add] at hCheckpoint
  unfold Collatz2.Word.prefixTwoDepth
    AdjacentFerrersSwap.rankUpperExponentWord
    AdjacentFerrersSwap.rankLowerExponentWord
  exact hCheckpoint

/-- selected 以外では normalized cut term 自身が exact に不変。 -/
theorem normalizedCutTerm_rankUpper_eq_rankLower_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    Collatz2.Word.normalizedCutTerm S.edge.rankUpperExponentWord k =
      Collatz2.Word.normalizedCutTerm S.edge.rankLowerExponentWord k := by
  have hDepth :=
    S.prefixTwoDepth_rankUpper_eq_rankLower_of_ne_rankCut hLowerFP hk
  unfold Collatz2.Word.normalizedCutTerm
  rw [hDepth]
  rw [S.edge.rankUpperExponentWord_oddSteps]
  rw [S.edge.rankLowerExponentWord_oddSteps]

/-- first-passage cell cost は contracting だけで strict positive。 -/
theorem fareyCellCost_pos
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    0 < S.edge.fareyCellCost := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hContract : 3 ^ S.edge.oddTotal < S.edge.modulus := by
    have h := hEdgeLowerFP.2.2
    unfold CoefficientContracting at h
    simpa [AdjacentFerrersSwap.modulus] using h
  exact S.edge.fareyCellCost_pos_of_contracting hContract

/-- positive integer cell cost と `toNat` の exact cast。 -/
theorem fareyCellCost_toNat_cast
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    (S.edge.fareyCellCost.toNat : ℤ) = S.edge.fareyCellCost := by
  rw [Int.toNat_of_nonneg (le_of_lt (S.fareyCellCost_pos hLowerFP))]

/-- selected upper top representative は ordinary `3*C mod G`。 -/
theorem selected_rankTopRepresentative_upper_eq_residue3
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    let hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
    let hF := S.edge.rankUpperExponentWord_firstCrossing hUpperFP
    let G := Collatz2.Word.terminalGap S.edge.rankUpperExponentWord
    let C := S.edge.fareyCellCost.toNat
    Collatz2.Word.rankTopRepresentative hF S.edge.rankCut =
      rankTopResidue3 G C := by
  let hUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
  let hF := S.edge.rankUpperExponentWord_firstCrossing hUpperFP
  let G := Collatz2.Word.terminalGap S.edge.rankUpperExponentWord
  let C := S.edge.fareyCellCost.toNat
  have hGPos : 0 < G := by
    dsimp [G, Collatz2.Word.terminalGap]
    exact
      Collatz2.AffineTransfer.centerGap_pos_of_negative
        hF.terminalNegative
  let : NeZero G :=
    ⟨Nat.ne_of_gt hGPos⟩
  have hU :=
    S.edge.universalCutWeight_rankCut_eq_three_mul_fareyCellCost
      hUpperFP
  have hCostZ :=
    S.fareyCellCost_toNat_cast hLowerFP
  have hCostCast :
      (((S.edge.fareyCellCost.toNat : ℕ) : ℤ) : ZMod G) =
        (S.edge.fareyCellCost : ZMod G) :=
    congrArg
      (fun z : ℤ => (z : ZMod G))
      hCostZ
  have hCostCast' :
      (S.edge.fareyCellCost : ZMod G) =
        (C : ZMod G) := by
    calc
      (S.edge.fareyCellCost : ZMod G)
          =
        (((S.edge.fareyCellCost.toNat : ℕ) : ℤ) : ZMod G) :=
          hCostCast.symm
      _ = (S.edge.fareyCellCost.toNat : ZMod G) := by
        exact Int.cast_natCast _
      _ = (C : ZMod G) := by
        rfl
  have hUNat :
      Collatz2.Word.universalCutWeight hF S.edge.rankCut =
        (((3 * C : ℕ)) : ZMod G) := by
    calc
      Collatz2.Word.universalCutWeight hF S.edge.rankCut
          =
        3 * (S.edge.fareyCellCost : ZMod G) := by
          simpa [hF, G] using hU
      _ = 3 * (C : ZMod G) := by
        rw [hCostCast']
      _ = (((3 * C : ℕ)) : ZMod G) := by
        norm_num
  have hVal :
      (Collatz2.Word.universalCutWeight hF S.edge.rankCut).val =
        (((3 * C : ℕ) : ZMod G)).val :=
    congrArg ZMod.val hUNat
  rw [ZMod.val_natCast] at hVal
  simpa [
    Collatz2.Word.rankTopRepresentative,
    rankTopResidue3,
    G,
    C
  ] using hVal

/-- selected lower top representative は ordinary `6*C mod G`。 -/
theorem selected_rankTopRepresentative_lower_eq_residue6
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
    let hF := S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
    let G := Collatz2.Word.terminalGap S.edge.rankLowerExponentWord
    let C := S.edge.fareyCellCost.toNat
    Collatz2.Word.rankTopRepresentative hF S.edge.rankCut =
      rankTopResidue6 G C := by
  let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  let hF := S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  let G := Collatz2.Word.terminalGap S.edge.rankLowerExponentWord
  let C := S.edge.fareyCellCost.toNat
  have hGPos : 0 < G := by
    dsimp [G, Collatz2.Word.terminalGap]
    exact
      Collatz2.AffineTransfer.centerGap_pos_of_negative
        hF.terminalNegative
  let : NeZero G :=
    ⟨Nat.ne_of_gt hGPos⟩
  have hU :=
    S.edge.rankLower_universalCutWeight_rankCut_eq_six_mul_fareyCellCost
      hEdgeLowerFP
  have hCostZ :=
    S.fareyCellCost_toNat_cast hLowerFP
  have hCostCast :
      (((S.edge.fareyCellCost.toNat : ℕ) : ℤ) : ZMod G) =
        (S.edge.fareyCellCost : ZMod G) :=
    congrArg
      (fun z : ℤ => (z : ZMod G))
      hCostZ
  have hCostCast' :
      (S.edge.fareyCellCost : ZMod G) =
        (C : ZMod G) := by
    calc
      (S.edge.fareyCellCost : ZMod G)
          =
        (((S.edge.fareyCellCost.toNat : ℕ) : ℤ) : ZMod G) :=
          hCostCast.symm
      _ = (S.edge.fareyCellCost.toNat : ZMod G) := by
        simp only [Int.cast_natCast]
      _ = (C : ZMod G) := by
        rfl
  have hUNat :
      Collatz2.Word.universalCutWeight hF S.edge.rankCut =
        (((6 * C : ℕ)) : ZMod G) := by
    calc
      Collatz2.Word.universalCutWeight hF S.edge.rankCut
          =
        6 * (S.edge.fareyCellCost : ZMod G) := by
          simpa [hF, G] using hU
      _ = 6 * (C : ZMod G) := by
        rw [hCostCast']
      _ = (((6 * C : ℕ)) : ZMod G) := by
        norm_num
  have hVal :
      (Collatz2.Word.universalCutWeight hF S.edge.rankCut).val =
        (((6 * C : ℕ) : ZMod G)).val :=
    congrArg ZMod.val hUNat
  rw [ZMod.val_natCast] at hVal
  simpa [
    Collatz2.Word.rankTopRepresentative,
    rankTopResidue6,
    G,
    C
  ] using hVal

/--
等しい modulus の間で `ZMod` の値を transport する。
複雑な terminal-gap equality に対する dependent rewrite を局所化する。
-/
def zmodCongrTransport
    {G H : ℕ}
    (h : G = H) :
    ZMod G → ZMod H :=
  fun x => Eq.mp (congrArg ZMod h) x


/--
scaled equality を等しい modulus 側へ transport する。
-/
theorem zmodCongrTransport_scaled
    {G H a b : ℕ}
    (h : G = H)
    {x : ZMod G}
    (hx :
      (a : ZMod G) * x = (b : ZMod G)) :
    (a : ZMod H) * zmodCongrTransport h x =
      (b : ZMod H) := by
  cases h
  simpa [zmodCongrTransport] using hx


/--
modulus transport は ordinary representative `val` を変えない。
-/
theorem zmodCongrTransport_val
    {G H : ℕ}
    (h : G = H)
    [NeZero G]
    [NeZero H]
    (x : ZMod G) :
    (zmodCongrTransport h x).val = x.val := by
  cases h
  simp [zmodCongrTransport]

/--
selected cut 以外では upper / lower universal weight は、
共通 terminal gap への transport を除いて exact に一致する。
-/
theorem universalCutWeight_upper_eq_transport_lower_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
    let hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
    let hLowerF :=
      S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
    let hUpperF :=
      S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
    let hGap :=
      S.edge.rankLower_terminalGap_eq_rankUpper_terminalGap
        hEdgeLowerFP hEdgeUpperFP
    Collatz2.Word.universalCutWeight hUpperF k =
      zmodCongrTransport hGap
        (Collatz2.Word.universalCutWeight hLowerF k) := by
  let hEdgeLowerFP :=
    S.edge_lower_firstPassage hLowerFP
  let hEdgeUpperFP :=
    S.edge_upper_firstPassage_of_lower hLowerFP
  let hLowerF :=
    S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  let hUpperF :=
    S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
  let hGap :=
    S.edge.rankLower_terminalGap_eq_rankUpper_terminalGap
      hEdgeLowerFP hEdgeUpperFP
  have hTerm :=
    S.normalizedCutTerm_rankUpper_eq_rankLower_of_ne_rankCut
      hLowerFP hk
  have hUpperScaled :=
    hUpperF.threePow_mul_universalCutWeight k
  have hLowerScaled :=
    hLowerF.threePow_mul_universalCutWeight k
  rw [S.edge.rankUpperExponentWord_oddSteps] at hUpperScaled
  rw [S.edge.rankLowerExponentWord_oddSteps] at hLowerScaled
  rw [hTerm] at hUpperScaled
  have hLowerScaled' :
      (((3 ^ S.edge.oddTotal : ℕ)) :
          ZMod
            (Collatz2.Word.terminalGap
              S.edge.rankUpperExponentWord)) *
          zmodCongrTransport hGap
            (Collatz2.Word.universalCutWeight hLowerF k) =
        ((Collatz2.Word.normalizedCutTerm
            S.edge.rankLowerExponentWord k : ℕ) :
          ZMod
            (Collatz2.Word.terminalGap
              S.edge.rankUpperExponentWord)) := by
    exact
      zmodCongrTransport_scaled
        hGap
        hLowerScaled
  have hScaledEq :
      (((3 ^ S.edge.oddTotal : ℕ)) :
          ZMod
            (Collatz2.Word.terminalGap
              S.edge.rankUpperExponentWord)) *
          Collatz2.Word.universalCutWeight hUpperF k =
        (((3 ^ S.edge.oddTotal : ℕ)) :
          ZMod
            (Collatz2.Word.terminalGap
              S.edge.rankUpperExponentWord)) *
          zmodCongrTransport hGap
            (Collatz2.Word.universalCutWeight hLowerF k) :=
    hUpperScaled.trans hLowerScaled'.symm
  exact hUpperF.cancel_threePow (by
    simpa only [S.edge.rankUpperExponentWord_oddSteps] using hScaledEq)

/-- selected 以外の universal top ordinary representative は exact に不変。 -/
theorem rankTopRepresentative_upper_eq_lower_of_ne_rankCut
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {k : ℕ}
    (hk : k ≠ S.edge.rankCut) :
    let hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
    let hEdgeUpperFP := S.edge_upper_firstPassage_of_lower hLowerFP
    let hLowerF :=
      S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
    let hUpperF :=
      S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
    Collatz2.Word.rankTopRepresentative hUpperF k =
      Collatz2.Word.rankTopRepresentative hLowerF k := by
  let hEdgeLowerFP :=
    S.edge_lower_firstPassage hLowerFP
  let hEdgeUpperFP :=
    S.edge_upper_firstPassage_of_lower hLowerFP
  let hLowerF :=
    S.edge.rankLowerExponentWord_firstCrossing hEdgeLowerFP
  let hUpperF :=
    S.edge.rankUpperExponentWord_firstCrossing hEdgeUpperFP
  let hGap :=
    S.edge.rankLower_terminalGap_eq_rankUpper_terminalGap
      hEdgeLowerFP hEdgeUpperFP
  have hLowerGapPos :
      0 <
        Collatz2.Word.terminalGap
          S.edge.rankLowerExponentWord := by
    unfold Collatz2.Word.terminalGap
    exact
      Collatz2.AffineTransfer.centerGap_pos_of_negative
        hLowerF.terminalNegative
  have hUpperGapPos :
      0 <
        Collatz2.Word.terminalGap
          S.edge.rankUpperExponentWord := by
    unfold Collatz2.Word.terminalGap
    exact
      Collatz2.AffineTransfer.centerGap_pos_of_negative
        hUpperF.terminalNegative
  let :
      NeZero
        (Collatz2.Word.terminalGap
          S.edge.rankLowerExponentWord) :=
    ⟨Nat.ne_of_gt hLowerGapPos⟩
  let :
      NeZero
        (Collatz2.Word.terminalGap
          S.edge.rankUpperExponentWord) :=
    ⟨Nat.ne_of_gt hUpperGapPos⟩
  have hEq :
      Collatz2.Word.universalCutWeight hUpperF k =
        zmodCongrTransport hGap
          (Collatz2.Word.universalCutWeight hLowerF k) := by
    exact
      S.universalCutWeight_upper_eq_transport_lower_of_ne_rankCut
        hLowerFP hk
  have hValUpper :
      (Collatz2.Word.universalCutWeight hUpperF k).val =
        (zmodCongrTransport hGap
          (Collatz2.Word.universalCutWeight hLowerF k)).val :=
    congrArg ZMod.val hEq
  have hValTransport :
      (zmodCongrTransport hGap
          (Collatz2.Word.universalCutWeight hLowerF k)).val =
        (Collatz2.Word.universalCutWeight hLowerF k).val := by
    exact
      zmodCongrTransport_val
        hGap
        (Collatz2.Word.universalCutWeight hLowerF k)
  have hVal :
      (Collatz2.Word.universalCutWeight hUpperF k).val =
        (Collatz2.Word.universalCutWeight hLowerF k).val :=
    hValUpper.trans hValTransport
  simpa [
    Collatz2.Word.rankTopRepresentative,
    hUpperF,
    hLowerF
  ] using hVal

end FerrersStep

end CSTMicro
end Collatz2
