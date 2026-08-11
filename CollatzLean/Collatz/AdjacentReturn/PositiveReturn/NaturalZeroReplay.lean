import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.FirstOvershoot
import CollatzLean.Collatz.Canonical.FirstCrossingReduction

/-!
# first overshoot から自然に現れる j=0 sign-change packet

first overshoot cut `r` では、直前 boundary は endpoint 未満、cut boundary は endpoint 以上、
その一歩の exponent は1。

さらに cut `r` の suffix replay quotient が0なら、base-3 recurrence
`Q_r = 3 * Q_{r-1} + J_{r-1}` により
`Q_{r-1} = 0` と `J_{r-1} = 0` も同時に強制される。

従って内部 suffix は

  canonicalStart(1 :: v) < canonicalEnd(1 :: v)
  canonicalEnd(v) <= canonicalStart(v)

という一文字で符号が反転する canonical packet になる。
しかも head replay quotient はちょうど旧 prepend-one `j = 0`。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData

/--
first overshoot の一歩前後がともに canonical replay level 0 にある sign-change packet。
-/
structure NaturalZeroReplaySignChangeData
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) where
  cut : ℕ
  pred : ℕ
  cut_eq : cut = firstOvershootCut F
  pred_succ : pred + 1 = cut
  cut_lt : cut < F.length
  pred_boundary_lt_endpoint :
    boundaryValue F pred < F.endpointValue
  endpoint_le_cut_boundary :
    F.endpointValue ≤ boundaryValue F cut
  exponent_eq_one :
    O.exponent (R.startIndex + pred) = 1
  cutReplay_zero :
    (suffixReplay F cut).quotient = 0
  predReplay_zero :
    (suffixReplay F pred).quotient = 0
  predStart_eq :
    boundaryValue F pred = Word.canonicalStart (suffixWord F pred)
  predEnd_eq :
    F.endpointValue = Word.canonicalEnd (suffixWord F pred)
  cutStart_eq :
    boundaryValue F cut = Word.canonicalStart (suffixWord F cut)
  cutEnd_eq :
    F.endpointValue = Word.canonicalEnd (suffixWord F cut)
  suffix_eq :
    suffixWord F pred = 1 :: suffixWord F cut

namespace NaturalZeroReplaySignChangeData

/-- predecessor suffix は positive canonical return。 -/
theorem predecessor_positive
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.canonicalStart (suffixWord F D.pred) <
      Word.canonicalEnd (suffixWord F D.pred) := by
  rw [← D.predStart_eq, ← D.predEnd_eq]
  exact D.pred_boundary_lt_endpoint

/-- cut 後の canonical tail は nonpositive。 -/
theorem tail_nonpositive
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.canonicalEnd (suffixWord F D.cut) ≤
      Word.canonicalStart (suffixWord F D.cut) := by
  rw [← D.cutEnd_eq, ← D.cutStart_eq]
  exact D.endpoint_le_cut_boundary

/-- first overshoot の head replay digit 自身も0。 -/
theorem headDigit_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    headDigit F D.pred (by
      rw [D.pred_succ]
      exact D.cut_lt) = 0 := by
  have hk : D.pred + 1 < F.length := by
    rw [D.pred_succ]
    exact D.cut_lt
  have hrec :=
    suffixReplay_quotient_succ F D.pred hk
  have hcut :
      (suffixReplay F (D.pred + 1)).quotient = 0 := by
    rw [D.pred_succ]
    exact D.cutReplay_zero
  have hpred :
      (suffixReplay F D.pred).quotient = 0 :=
    D.predReplay_zero
  rw [hcut, hpred] at hrec
  omega

/-- cut 後 tail は非空。 -/
theorem tail_nonempty
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    suffixWord F D.cut ≠ [] := by
  apply List.ne_nil_of_length_pos
  simpa [suffixWord] using D.cut_lt

/--
この packet の一文字 head replay は、旧 `PrependOneReplayData` の quotient `j=0` を与える。
-/
theorem exists_prependOneReplayData_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ∃ boundary : ℕ,
      Word.PrependOneReplayData
        (suffixWord F D.cut) boundary 0 := by
  have hk : D.pred + 1 < F.length := by
    rw [D.pred_succ]
    exact D.cut_lt
  let H := headReplayData F D.pred hk
  let v := suffixWord F D.cut
  have hsuccZero :
      (suffixReplay F (D.pred + 1)).quotient = 0 := by
    rw [D.pred_succ]
    exact D.cutReplay_zero
  have hrec :
      (suffixReplay F (D.pred + 1)).quotient =
        H.replay.quotient +
          3 * (suffixReplay F D.pred).quotient := by
    simpa [H] using
      suffixReplay_quotient_succ_eq_headReplay F D.pred hk
  have hHq : H.replay.quotient = 0 := by
    omega
  have hhead :
      2 * H.boundary =
        3 * Word.canonicalStart (1 :: v) + 1 := by
    have h := H.headStep
    simpa [v, D.exponent_eq_one, D.pred_succ] using h
  have hboundaryMod :
      H.boundary % 3 = 2 := by
    omega
  refine ⟨H.boundary, ?_⟩
  exact {
    headStep := hhead

    suffixRuns := by
      have h := H.tailRuns
      simpa [v, D.exponent_eq_one, D.pred_succ] using h

    boundary_eq := by
      have h := H.replay.start_eq
      rw [hHq] at h
      simpa [v, D.pred_succ] using h

    endpoint_eq := by
      have h := H.replay.finish_eq
      rw [hHq] at h
      simpa [v, D.exponent_eq_one, D.pred_succ] using h

    quotient_le_two := by
      omega

    boundary_mod_three := hboundaryMod
  }

/--
自然 sign-change packet から得た旧 `j=0` replay は CORE condition を必ず破る。

これは旧 j=0 obstruction が PositiveReturn 内部から自然発生することの局所形。
-/
theorem not_prependOneCoreCondition_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ¬ Word.PrependOneCoreCondition (suffixWord F D.cut) 0 := by
  intro hCore
  obtain ⟨boundary, hReplay⟩ :=
    D.exists_prependOneReplayData_zero
  let v := suffixWord F D.cut
  have hwholePositive :
      Word.canonicalStart (1 :: v) <
        Word.canonicalEnd (1 :: v) := by
    have h := D.predecessor_positive
    rw [D.suffix_eq] at h
    simpa [v] using h
  have hboundary :
      boundary = Word.canonicalStart v := by
    have h := hReplay.boundary_eq
    simpa [v] using h
  have hendpoint :
      Word.canonicalEnd (1 :: v) =
        Word.canonicalEnd v := by
    have h := hReplay.endpoint_eq
    simpa [v] using h
  have hstartMod :
      Word.canonicalStart v % 3 = 2 := by
    rw [← hboundary]
    exact hReplay.boundary_mod_three
  have hhead :
      2 * Word.canonicalStart v =
        3 * Word.canonicalStart (1 :: v) + 1 := by
    have h := hReplay.headStep
    rw [hboundary] at h
    simpa [v] using h
  have hCore' := hCore
  change Word.PrependOneCoreCondition v 0 at hCore'
  unfold Word.PrependOneCoreCondition at hCore'
  simp only [Nat.mul_zero, Nat.add_zero] at hCore'
  have hnonpositive :
      Word.canonicalEnd (1 :: v) ≤
        Word.canonicalStart (1 :: v) := by
    rw [hendpoint]
    omega
  exact
    (Nat.not_le_of_gt hwholePositive) hnonpositive

end NaturalZeroReplaySignChangeData

/--
first overshoot cut の endpoint が suffix replay 一段分より小さければ、
自然な `j=0` sign-change packet が得られる。
-/
noncomputable def naturalZeroReplaySignChange_of_endpoint_lt
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R)
    (hsmall :
      F.endpointValue <
        2 * 3 ^ Word.oddSteps (suffixWord F (firstOvershootCut F))) :
    NaturalZeroReplaySignChangeData F := by
  let cut := firstOvershootCut F
  let pred := firstOvershootPred F
  have hcutEq : cut = firstOvershootCut F := rfl
  have hpredSucc : pred + 1 = cut := by
    have h := firstOvershootCut_eq_pred_add_one F
    simpa [cut, pred] using h.symm
  have hcutLt : cut < F.length := by
    simpa [cut] using firstOvershootCut_lt_length F
  have hpredLt : pred < cut := by omega
  have hpredNextLt : pred + 1 < F.length := by omega
  have hpredBound :
      boundaryValue F pred < F.endpointValue := by
    simpa [pred] using firstOvershootPred_boundary_lt_endpoint F
  have hcutBound :
      F.endpointValue ≤ boundaryValue F cut := by
    simpa [cut] using endpoint_le_firstOvershoot_boundary F
  have hExpOne :
      O.exponent (R.startIndex + pred) = 1 := by
    simpa [pred] using firstOvershootPred_exponent_eq_one F
  have hqCut : (suffixReplay F cut).quotient = 0 := by
    let Q := suffixReplay F cut
    apply Word.ReplayCoordinate.quotient_eq_zero_of_finish_lt_two_mul_threePow Q
    have hend := suffixEndValue_eq_endpoint F (Nat.le_of_lt hcutLt)
    rw [hend]
    simpa [cut] using hsmall
  have hrec := suffixReplay_quotient_succ F pred hpredNextLt
  rw [hpredSucc, hqCut] at hrec
  have hqPred : (suffixReplay F pred).quotient = 0 := by
    omega
  have hpredStart :
      boundaryValue F pred = Word.canonicalStart (suffixWord F pred) := by
    exact
      Word.ReplayCoordinate.start_eq_canonical_of_quotient_eq_zero
        (suffixReplay F pred) hqPred
  have hcutStart :
      boundaryValue F cut = Word.canonicalStart (suffixWord F cut) := by
    exact
      Word.ReplayCoordinate.start_eq_canonical_of_quotient_eq_zero
        (suffixReplay F cut) hqCut
  have hpredEnd :
      F.endpointValue = Word.canonicalEnd (suffixWord F pred) := by
    have hfinish := (suffixReplay F pred).finish_eq
    have hfinish' :
        suffixEndValue F pred = Word.canonicalEnd (suffixWord F pred) := by
      simpa [hqPred] using hfinish
    have hend := suffixEndValue_eq_endpoint F (by omega : pred ≤ F.length)
    calc
      F.endpointValue = suffixEndValue F pred := hend.symm
      _ = Word.canonicalEnd (suffixWord F pred) := hfinish'
  have hcutEnd :
      F.endpointValue = Word.canonicalEnd (suffixWord F cut) := by
    have hfinish := (suffixReplay F cut).finish_eq
    have hfinish' :
        suffixEndValue F cut = Word.canonicalEnd (suffixWord F cut) := by
      simpa [hqCut] using hfinish
    have hend := suffixEndValue_eq_endpoint F (Nat.le_of_lt hcutLt)
    calc
      F.endpointValue = suffixEndValue F cut := hend.symm
      _ = Word.canonicalEnd (suffixWord F cut) := hfinish'
  have hsuffix : suffixWord F pred = 1 :: suffixWord F cut := by
    have h := suffixWord_eq_cons F (by omega : pred < F.length)
    rw [hExpOne, hpredSucc] at h
    exact h
  exact {
    cut := cut
    pred := pred
    cut_eq := hcutEq
    pred_succ := hpredSucc
    cut_lt := hcutLt
    pred_boundary_lt_endpoint := hpredBound
    endpoint_le_cut_boundary := hcutBound
    exponent_eq_one := hExpOne
    cutReplay_zero := hqCut
    predReplay_zero := hqPred
    predStart_eq := hpredStart
    predEnd_eq := hpredEnd
    cutStart_eq := hcutStart
    cutEnd_eq := hcutEnd
    suffix_eq := hsuffix
  }

end FirstCrossingData
end PositiveReturn
end AdjacentReturn
end Collatz
