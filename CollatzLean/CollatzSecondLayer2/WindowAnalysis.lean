import CollatzLean.CollatzSecondLayer2.SpecialC3
import CollatzLean.CollatzFirstLayer.DownwardReplay



/-!
# prepared q-windowの有限分岐

差深さがlower側次指数以下であるprepared windowを、

* captured carry
* lower natural replay
* positive predecessor shadow
* zero-sync Special C3

へ完全分類する。旧SecondLayerのpacket分岐を、actual moving window上へ直接移した形である。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit

/-- first-carry二分岐とcanonical replayを適用できるprepared window。 -/
structure PreparedWindowPacket (O : OddOrbit) (i q : ℕ)
    extends WindowDifferenceData O i q where
  length_pos : 0 < q
  depth_le_nextExponent : depth ≤ O.exponent i

namespace PreparedWindowPacket

/-- packetが保存するactual q-run。 -/
theorem run
    {O : OddOrbit} {i q : ℕ}
    (_P : PreparedWindowPacket O i q) :
    Runs (O.segmentWord i q) (O.value i) (O.value (i + q)) :=
  O.runs_segment i q

/-- packetのq-wordは非空。 -/
theorem word_nonempty
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q) :
    O.segmentWord i q ≠ [] := by
  intro hnil
  have hq : 0 < q := P.length_pos
  have hlen : q = 0 := by
    simpa using congrArg List.length hnil
  omega

/-- packetのcanonical replay座標。 -/
def replayCoordinate
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q) :
    CanonicalReplayCoordinate
      (O.segmentWord i q) (O.value i) (O.value (i + q)) :=
  canonicalReplayCoordinate_of_runs P.run P.word_nonempty

end PreparedWindowPacket

/-- Special C3へ入る前に有限windowから脱出する三種類。 -/
inductive PreparedWindowAlternative
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q) : Type
  | captured (data : CapturedWindowAt O i q)
  | lowerNaturalReplay
      (data : LowerNaturalRunReplayData
        (O.segmentWord i q) (O.value i) (O.value (i + q)))
  | positivePredecessorShadow
      (canonicalBoundary : P.replayCoordinate.quotient = 0)
      (data : 0 < predecessorShadow (O.segmentWord i q))

namespace PreparedWindowAlternative

/-- lower natural replay枝では元終点が`2*3^q`を真に超える。 -/
theorem endpoint_gt_two_mul_threePow_of_lowerReplay
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q)
    (L : LowerNaturalRunReplayData
      (O.segmentWord i q) (O.value i) (O.value (i + q))) :
    2 * 3 ^ q < O.value (i + q) := by
  have hodd : Odd L.lowerFinish :=
    L.lowerRuns.end_odd_of_ne_nil P.word_nonempty
  have hpos : 0 < L.lowerFinish := by
    rcases hodd with ⟨k, hk⟩
    omega
  rw [L.finish_step]
  simpa [oddSteps] using
    (show 2 * 3 ^ q < L.lowerFinish + 2 * 3 ^ q by omega)

/-- positive predecessor shadow枝でも元終点が`2*3^q`を真に超える。 -/
theorem endpoint_gt_two_mul_threePow_of_positiveShadow
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q)
    (hq : P.replayCoordinate.quotient = 0)
    (hpos : 0 < predecessorShadow (O.segmentWord i q)) :
    2 * 3 ^ q < O.value (i + q) := by
  have hend :
      O.value (i + q) = canonicalEnd (O.segmentWord i q) := by
    rw [P.replayCoordinate.finish_eq, hq]
    simp
  have hZ :=
    (predecessorShadow_pos_iff (O.segmentWord i q)).mp hpos
  have hNat0 :
      2 * 3 ^ oddSteps (O.segmentWord i q) <
        canonicalEnd (O.segmentWord i q) := by
    exact_mod_cast hZ
  have hNat :
      2 * 3 ^ q < canonicalEnd (O.segmentWord i q) := by
    simpa [oddSteps] using hNat0
  simpa [hend]

end PreparedWindowAlternative

/-- prepared packetをcaptureかdeferredへ分ける。 -/
theorem preparedWindow_capture_or_deferred
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q) :
    Nonempty
      (CapturedWindowAt O i q ⊕ DeferredWindowAt O i q) := by
  rcases lt_or_eq_of_le P.depth_le_nextExponent with hlt | heq
  · exact ⟨Sum.inl
      { toWindowDifferenceData := P.toWindowDifferenceData
        captured := hlt }⟩
  · exact ⟨Sum.inr
      { toWindowDifferenceData := P.toWindowDifferenceData
        deferred := heq }⟩

/--
各prepared windowはalternative exitまたはzero-sync Special C3へ落ちる。
-/
theorem preparedWindowAnalysis_nonempty
    {O : OddOrbit} {i q : ℕ}
    (P : PreparedWindowPacket O i q) :
    Nonempty
      (PreparedWindowAlternative P ⊕ SpecialC3At O i q) := by
  rcases preparedWindow_capture_or_deferred P with ⟨hcap | hdefer⟩
  · exact ⟨Sum.inl (PreparedWindowAlternative.captured hcap)⟩
  · let C := P.replayCoordinate
    by_cases hq : C.quotient = 0
    · have hstart :
          O.value i = canonicalStart (O.segmentWord i q) :=
        C.start_eq_canonical_of_quotient_eq_zero hq
      have hend :
          O.value (i + q) = canonicalEnd (O.segmentWord i q) := by
        rw [C.finish_eq, hq]
        simp
      rcases lt_trichotomy
          (predecessorShadow (O.segmentWord i q)) 0 with
        hneg | hzero | hpos
      · exact ⟨Sum.inr
          (specialC3At_of_deferred hdefer P.length_pos
            hstart hend hneg)⟩
      · exact False.elim
          ((predecessorShadow_ne_zero (O.segmentWord i q)) hzero)
      · exact ⟨Sum.inl
          (PreparedWindowAlternative.positivePredecessorShadow hq hpos)⟩
    · have hqpos : 0 < C.quotient := Nat.pos_of_ne_zero hq
      exact ⟨Sum.inl
        (PreparedWindowAlternative.lowerNaturalReplay
          (C.lowerNaturalRunReplay P.run hqpos))⟩

end OddOrbit
end CollatzSecondLayer2
