import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Cumulative
import CollatzLean.Collatz.Canonical.Cylinder

/-!
# positive return の suffix replay profile

一段目の prepend-one quotient だけでなく、first crossing の各 head deletion に
canonical replay quotient を置く。隣接 quotient は base-3 型 recurrence を満たす。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

private theorem residueModulus_cons_eq
    (e : ℕ) (v : Collatz.Word) :
    Word.residueModulus (e :: v) =
      2 ^ e * Word.residueModulus v := by
  unfold Word.residueModulus
  simp only [Word.twoSteps_cons]
  rw [show e + Word.twoSteps v + 1 = e + (Word.twoSteps v + 1) by omega]
  rw [pow_add]

/--
canonical word を一文字進めた境界を tail の canonical replay 座標で表す。
その quotient は exponent の値によらず `0,1,2` の三値しかない。
-/
structure CanonicalHeadReplayData (e : ℕ) (v : Collatz.Word) where
  boundary : ℕ
  headStep :
    2 ^ e * boundary = 3 * Word.canonicalStart (e :: v) + 1
  tailRuns :
    Word.Runs v boundary (Word.canonicalEnd (e :: v))
  replay :
    Word.ReplayCoordinate v boundary (Word.canonicalEnd (e :: v))
  quotient_le_two : replay.quotient ≤ 2

namespace CanonicalHeadReplayData

/-- valid な非空 tail を持つ canonical word から head replay data を作る。 -/
noncomputable def ofValid
    {e : ℕ} {v : Collatz.Word}
    (hvalid : Word.Valid (e :: v))
    (hvne : v ≠ []) :
    CanonicalHeadReplayData e v := by
  have hrun :
      Word.Runs
        (e :: v)
        (Word.canonicalStart (e :: v))
        (Word.canonicalEnd (e :: v)) :=
    hvalid.canonicalRuns
  refine Classical.choice ?_
  -- ここからゴールは Prop なので Runs を cases できる。
  change Nonempty (CanonicalHeadReplayData e v)
  cases hrun with
  | @cons e v x boundary z he hstep hodd htail =>
      let Q :
          Word.ReplayCoordinate
            v boundary (Word.canonicalEnd (e :: v)) :=
        Word.ReplayCoordinate.ofRuns htail hvne
      have hmodulus :
          Word.residueModulus (e :: v) =
            2 ^ e * Word.residueModulus v :=
        residueModulus_cons_eq e v
      have hstartLt :
          Word.canonicalStart (e :: v) <
            2 ^ e * Word.residueModulus v := by
        rw [← hmodulus]
        exact Word.canonicalStart_lt_modulus (e :: v)
      have hboundaryLt :
          boundary < 3 * Word.residueModulus v := by
        by_contra hnot
        have hge :
            3 * Word.residueModulus v ≤ boundary :=
          Nat.le_of_not_gt hnot
        have hmul :=
          Nat.mul_le_mul_left (2 ^ e) hge
        have hcontra :
            3 * (2 ^ e * Word.residueModulus v) ≤
              3 * Word.canonicalStart (e :: v) + 1 := by
          calc
            3 * (2 ^ e * Word.residueModulus v)
                = 2 ^ e * (3 * Word.residueModulus v) := by ring
            _ ≤ 2 ^ e * boundary := hmul
            _ = 3 * Word.canonicalStart (e :: v) + 1 := hstep
        omega
      have hqLe : Q.quotient ≤ 2 := by
        by_contra hnot
        have hqThree : 3 ≤ Q.quotient := by
          omega
        have hmul :=
          Nat.mul_le_mul_left
            (Word.residueModulus v) hqThree
        have hboundaryGe :
            3 * Word.residueModulus v ≤ boundary := by
          calc
            3 * Word.residueModulus v
                = Word.residueModulus v * 3 := by ring
            _ ≤ Word.residueModulus v * Q.quotient := hmul
            _ ≤ Word.canonicalStart v +
                  Word.residueModulus v * Q.quotient := by
              omega
            _ = boundary := Q.start_eq.symm
        omega
      exact ⟨{
        boundary := boundary
        headStep := hstep
        tailRuns := htail
        replay := Q
        quotient_le_two := hqLe
      }⟩

end CanonicalHeadReplayData

namespace FirstCrossingData

/-- cut `k` 以後の actual suffix word。 -/
def suffixWord
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) : Collatz.Word :=
  O.segment (R.startIndex + k) (F.length - k)

/-- cut `k` の actual odd boundary。 -/
def boundaryValue
    {O : OddOrbit} {R : State O}
    (_F : FirstCrossingData R) (k : ℕ) : ℕ :=
  O.value (R.startIndex + k)

/-- suffix segment の actual endpoint。 -/
def suffixEndValue
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) : ℕ :=
  O.value ((R.startIndex + k) + (F.length - k))

/-- 各 head deletion に対する canonical replay 座標。 -/
def suffixReplay
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) :
    Word.ReplayCoordinate
      (suffixWord F k)
      (boundaryValue F k)
      (suffixEndValue F k) := by
  exact
    Word.ReplayCoordinate.ofRealization
      (by
        simpa [suffixWord, boundaryValue, suffixEndValue] using
          O.realizesSegment (R.startIndex + k) (F.length - k))
      (by
        simpa [suffixEndValue] using
          O.value_odd ((R.startIndex + k) + (F.length - k)))

/-- `k≤length` なら suffix endpoint は元 first crossing endpoint と一致。 -/
theorem suffixEndValue_eq_endpoint
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {k : ℕ}
    (hk : k ≤ F.length) :
    suffixEndValue F k = F.endpointValue := by
  unfold suffixEndValue
  unfold FirstCrossingData.endpointValue
  have hindex :
      (R.startIndex + k) + (F.length - k) =
        R.startIndex + F.length := by omega
  rw [hindex]

/-- proper cut では suffix word を head と次 suffix に分解できる。 -/
theorem suffixWord_eq_cons
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {k : ℕ}
    (hk : k < F.length) :
    suffixWord F k =
      O.exponent (R.startIndex + k) :: suffixWord F (k + 1) := by
  unfold suffixWord
  have hlen :
      F.length - k = (F.length - (k + 1)) + 1 := by omega
  rw [hlen, O.segment_succ]
  simp only [Nat.add_assoc]

/-- 次 suffix が非空な cut に canonical head replay data を付ける。 -/
noncomputable def headReplayData
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) :
    CanonicalHeadReplayData
      (O.exponent (R.startIndex + k))
      (suffixWord F (k + 1)) := by
  have hk0 : k < F.length := by omega
  have hword := suffixWord_eq_cons F hk0
  have hvalidSuffix : Word.Valid (suffixWord F k) :=
    (O.runsSegment (R.startIndex + k) (F.length - k)).valid
  have hvalid :
      Word.Valid
        (O.exponent (R.startIndex + k) :: suffixWord F (k + 1)) := by
    rw [← hword]
    exact hvalidSuffix
  have htailne : suffixWord F (k + 1) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [suffixWord]
    omega
  exact CanonicalHeadReplayData.ofValid hvalid htailne

/-- cut `k` の一文字 head replay digit。 -/
noncomputable def headDigit
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) : ℕ :=
  (headReplayData F k hk).replay.quotient

/-- 各 head digit は `0,1,2` の三値。 -/
theorem headDigit_le_two
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) :
    headDigit F k hk ≤ 2 := by
  exact (headReplayData F k hk).quotient_le_two

/--
連続する suffix の実際の boundary value の recurrence。

head replay の canonical boundary と、
現在の suffix replay quotient から次の boundary を復元する。
-/
theorem boundaryValue_succ_eq_headReplay
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) :
    boundaryValue F (k + 1) =
      (headReplayData F k hk).boundary +
        3 * Word.residueModulus (suffixWord F (k + 1)) *
          (suffixReplay F k).quotient := by
  let e := O.exponent (R.startIndex + k)
  let v := suffixWord F (k + 1)
  let M := Word.residueModulus v
  let P := 2 ^ e
  let q : ℕ := (suffixReplay F k).quotient
  let H := headReplayData F k hk
  have hk0 : k < F.length := by
    omega
  have hword :
      suffixWord F k = e :: v := by
    simpa [e, v] using suffixWord_eq_cons F hk0
  have hmodulus :
      Word.residueModulus (e :: v) = P * M := by
    simpa [P, M] using residueModulus_cons_eq e v
  have hcanonical :
      Word.canonicalStart (suffixWord F k) =
        Word.canonicalStart (e :: v) :=
    congrArg Word.canonicalStart hword
  have hsuffixModulus :
      Word.residueModulus (suffixWord F k) =
        P * M := by
    calc
      Word.residueModulus (suffixWord F k)
          = Word.residueModulus (e :: v) :=
            congrArg Word.residueModulus hword
      _ = P * M := hmodulus
  have hQstart :
      boundaryValue F k =
        Word.canonicalStart (e :: v) +
          (P * M) * q := by
    calc
      boundaryValue F k
          =
          Word.canonicalStart (suffixWord F k) +
            Word.residueModulus (suffixWord F k) * q := by
            simpa [q] using (suffixReplay F k).start_eq
      _ =
          Word.canonicalStart (e :: v) +
            (P * M) * q := by
            rw [hcanonical, hsuffixModulus]
  have hHstep :
      P * H.boundary =
        3 * Word.canonicalStart (e :: v) + 1 := by
    simpa [H, P, e, v] using H.headStep
  have hactual :
      P * boundaryValue F (k + 1) =
        3 * boundaryValue F k + 1 := by
    simpa [P, e, boundaryValue, Nat.add_assoc] using
      O.step (R.startIndex + k)
  have hscaled :
      P * boundaryValue F (k + 1) =
        P * (H.boundary + 3 * M * q) := by
    calc
      P * boundaryValue F (k + 1)
          = 3 * boundaryValue F k + 1 := hactual
      _ =
          3 *
            (Word.canonicalStart (e :: v) +
              (P * M) * q) + 1 := by
            rw [hQstart]
      _ =
          (3 * Word.canonicalStart (e :: v) + 1) +
            3 * P * M * q := by
            ring
      _ =
          P * H.boundary +
            3 * P * M * q := by
            rw [← hHstep]
      _ =
          P * (H.boundary + 3 * M * q) := by
            ring
  have hPpos : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by omega)
  have hboundary :
      boundaryValue F (k + 1) =
        H.boundary + 3 * M * q :=
    Nat.mul_left_cancel hPpos hscaled
  simpa [H, M, q] using hboundary

/--
連続する suffix replay quotient の recurrence を
head replay quotient を用いて表す。

`Q_{k+1} = H_k + 3*Q_k`。
-/
theorem suffixReplay_quotient_succ_eq_headReplay
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) :
    (suffixReplay F (k + 1)).quotient =
      (headReplayData F k hk).replay.quotient +
        3 * (suffixReplay F k).quotient := by
  let v := suffixWord F (k + 1)
  let M := Word.residueModulus v
  let Q := suffixReplay F k
  let Qnext := suffixReplay F (k + 1)
  let H := headReplayData F k hk
  have hQnextStart :
      boundaryValue F (k + 1) =
        Word.canonicalStart v + M * Qnext.quotient := by
    simpa [Qnext, v, M] using Qnext.start_eq
  have hHstart :
      H.boundary =
        Word.canonicalStart v + M * H.replay.quotient := by
    simpa [H, v, M] using H.replay.start_eq
  have hboundary :
      boundaryValue F (k + 1) =
        H.boundary + 3 * M * Q.quotient := by
    simpa [H, M, Q] using
      boundaryValue_succ_eq_headReplay F k hk
  have hstartEq :
      Word.canonicalStart v + M * Qnext.quotient =
        Word.canonicalStart v +
          M * (H.replay.quotient + 3 * Q.quotient) := by
    calc
      Word.canonicalStart v + M * Qnext.quotient
          = boundaryValue F (k + 1) := hQnextStart.symm
      _ = H.boundary + 3 * M * Q.quotient := hboundary
      _ = (Word.canonicalStart v + M * H.replay.quotient) +
            3 * M * Q.quotient := by
            exact congrArg
              (fun x : ℕ => x + 3 * M * Q.quotient)
              hHstart
      _ = Word.canonicalStart v +
            M * (H.replay.quotient + 3 * Q.quotient) := by
            ring
  have hmul :
      M * Qnext.quotient =
        M * (H.replay.quotient + 3 * Q.quotient) :=
    Nat.add_left_cancel hstartEq
  have hMpos : 0 < M := by
    dsimp [M]
    simp [Word.residueModulus]
  have hq :
      Qnext.quotient =
        H.replay.quotient + 3 * Q.quotient :=
    Nat.mul_left_cancel hMpos hmul
  simpa [Qnext, H, Q] using hq

/--
連続する suffix replay quotient の base-3 recurrence。

`Q_{k+1} = 3*Q_k + J_k`。
-/
theorem suffixReplay_quotient_succ
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ)
    (hk : k + 1 < F.length) :
    (suffixReplay F (k + 1)).quotient =
      3 * (suffixReplay F k).quotient +
        headDigit F k hk := by
  have h :=
    suffixReplay_quotient_succ_eq_headReplay F k hk
  have hdigit :
      headDigit F k hk =
        (headReplayData F k hk).replay.quotient := by
    rfl
  rw [hdigit]
  omega

end FirstCrossingData

namespace Word.ReplayCoordinate

/-- finish が canonical replay 1段分より小さければ quotient は0。 -/
theorem quotient_eq_zero_of_finish_lt_two_mul_threePow
    {w : Collatz.Word} {X Y : ℕ}
    (Q : Word.ReplayCoordinate w X Y)
    (hsmall : Y < 2 * 3 ^ w.oddSteps) :
    Q.quotient = 0 := by
  by_contra hnot
  have hq : 1 ≤ Q.quotient := by omega
  have hmul :
      2 * 3 ^ w.oddSteps ≤
        (2 * 3 ^ w.oddSteps) * Q.quotient := by
    simpa using Nat.mul_le_mul_left (2 * 3 ^ w.oddSteps) hq
  have hfinish := Q.finish_eq
  have hle : 2 * 3 ^ w.oddSteps ≤ Y := by
    rw [hfinish]
    omega
  omega

end Word.ReplayCoordinate

namespace CanonicalChain

/-- positive-return chain では full first crossing の suffix replay level は0。 -/
theorem initial_suffixReplay_quotient_eq_zero
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    (FirstCrossingData.suffixReplay (C.firstCrossing n) 0).quotient = 0 := by
  let F := C.firstCrossing n
  let Q := FirstCrossingData.suffixReplay F 0
  have hword : FirstCrossingData.suffixWord F 0 = C.word n := by
    have h := F.word_eq_segment
    simpa [FirstCrossingData.suffixWord, word] using h.symm
  have hstart :
      FirstCrossingData.boundaryValue F 0
        = Word.canonicalStart (FirstCrossingData.suffixWord F 0) := by
    calc
      FirstCrossingData.boundaryValue F 0 = (C.state n).startValue := by
        simp [FirstCrossingData.boundaryValue, State.startValue]
      _ = Word.canonicalStart (C.word n) := C.start_eq_canonicalStart n
      _ = Word.canonicalStart (FirstCrossingData.suffixWord F 0) := by rw [hword]
  exact Q.quotient_eq_zero_of_start_eq_canonical (by simpa [Q] using hstart)

/-- endpoint が suffix replay 1段分より小さければ、その head deletion も canonical。 -/
theorem suffixReplay_quotient_eq_zero_of_endpoint_lt
    {O : OddOrbit} (C : CanonicalChain O) (n k : ℕ)
    (hk : k ≤ (C.firstCrossing n).length)
    (hsmall :
      (C.firstCrossing n).endpointValue <
        2 * 3 ^ (FirstCrossingData.suffixWord (C.firstCrossing n) k).oddSteps) :
    (FirstCrossingData.suffixReplay (C.firstCrossing n) k).quotient = 0 := by
  let F := C.firstCrossing n
  let Q := FirstCrossingData.suffixReplay F k
  apply Word.ReplayCoordinate.quotient_eq_zero_of_finish_lt_two_mul_threePow Q
  have hend := FirstCrossingData.suffixEndValue_eq_endpoint F hk
  rw [hend]
  exact hsmall

/-- quotient zero なら cut boundary と endpoint は suffix の canonical start/end。 -/
theorem suffix_canonical_of_endpoint_lt
    {O : OddOrbit} (C : CanonicalChain O) (n k : ℕ)
    (hk : k ≤ (C.firstCrossing n).length)
    (hsmall :
      (C.firstCrossing n).endpointValue <
        2 * 3 ^
          Word.oddSteps
            (FirstCrossingData.suffixWord
              (C.firstCrossing n) k)) :
    FirstCrossingData.boundaryValue
        (C.firstCrossing n) k =
      Word.canonicalStart
        (FirstCrossingData.suffixWord
          (C.firstCrossing n) k) ∧
    (C.firstCrossing n).endpointValue =
      Word.canonicalEnd
        (FirstCrossingData.suffixWord
          (C.firstCrossing n) k) := by
  let F := C.firstCrossing n
  let Q := FirstCrossingData.suffixReplay F k
  have hq : Q.quotient = 0 := by
    exact
      suffixReplay_quotient_eq_zero_of_endpoint_lt
        C n k hk hsmall
  have hstart :
      FirstCrossingData.boundaryValue F k =
        Word.canonicalStart
          (FirstCrossingData.suffixWord F k) := by
    have h :=
      Word.ReplayCoordinate.start_eq_canonical_of_quotient_eq_zero
        Q hq
    simpa [Q] using h
  have hfinish :
      FirstCrossingData.suffixEndValue F k =
        Word.canonicalEnd
          (FirstCrossingData.suffixWord F k) := by
    have h := Q.finish_eq
    simpa [Q, hq] using h
  have hend :
      FirstCrossingData.suffixEndValue F k =
        F.endpointValue :=
    FirstCrossingData.suffixEndValue_eq_endpoint F hk
  constructor
  · simpa [F] using hstart
  · calc
      (C.firstCrossing n).endpointValue
          = F.endpointValue := by
              rfl
      _ = FirstCrossingData.suffixEndValue F k :=
            hend.symm
      _ = Word.canonicalEnd
            (FirstCrossingData.suffixWord F k) :=
            hfinish
      _ = Word.canonicalEnd
            (FirstCrossingData.suffixWord
              (C.firstCrossing n) k) := by
            rfl

end CanonicalChain

end PositiveReturn
end AdjacentReturn
end Collatz
