import CollatzLean.Collatz.AdjacentReturn.FirstCrossingArithmetic
import CollatzLean.Collatz.Canonical.CylinderDerived

/-!
# contracting first crossingのcanonical化とLate zero-cylinder

Baker型gap下界とcontracting replay gapを組み合わせ、
十分長いactual first crossingのreplay quotientが0であることを示す。
Late項ではその後のsuffix全体がzero-cylinderになる。
-/

namespace Collatz
namespace AdjacentReturn

open Word

private theorem firstCrossing_three_mul_canonicalGap_lt_length
    {w : Collatz.Word}
    (hF : w.FirstCrossing)
    (hpos : w.canonicalStart < w.canonicalEnd) :
    3 * (w.canonicalEnd - w.canonicalStart) < w.length := by
  let d := w.canonicalEnd - w.canonicalStart
  let g := 2 ^ w.twoSteps - 3 ^ w.length
  /-
  first crossing の終端語は contracting。
  したがって 3^length < 2^twoSteps。
  -/
  have hC : w.Contracting :=
    hF.terminalContracting
  have hcontract :
      3 ^ w.length < 2 ^ w.twoSteps := by
    unfold Contracting at hC
    simpa [Word.oddSteps] using hC
  /-
  contracting gap
    g = 2^twoSteps - 3^length
  は真に正。
  -/
  have hg : 0 < g := by
    dsimp [g]
    omega
  /-
  canonical end は正。
  -/
  have hendPos : 0 < w.canonicalEnd :=
    w.canonicalEnd_pos
  /-
  d = canonicalEnd - canonicalStart と
  canonicalStart < canonicalEnd から、
    canonicalEnd = canonicalStart + d
  を得る。
  -/
  have hend :
      w.canonicalEnd = w.canonicalStart + d := by
    dsimp [d]
    rw [Nat.add_comm]
    exact (Nat.sub_add_cancel hpos.le).symm
  /-
  g の定義と contracting 性から、
    2^twoSteps = 3^length + g
  と書ける。
  -/
  have htwo :
      2 ^ w.twoSteps = 3 ^ w.length + g := by
    dsimp [g]
    omega
  /-
  canonical start/end は word の affine relation を実現する。
  -/
  have hreal :
      2 ^ w.twoSteps * w.canonicalEnd =
        3 ^ w.length * w.canonicalStart +
          w.affineConst := by
    simpa [Word.Realizes, Word.oddSteps] using
      w.canonicalEnd_realizes
  /-
  affine constant を canonical gap d と contracting gap g に分解する：

    affineConst
      = 3^length * d + g * canonicalEnd.
  -/
  have hid :
      w.affineConst =
        3 ^ w.length * d + g * w.canonicalEnd := by
    have hcancel :
        3 ^ w.length * w.canonicalStart +
            (3 ^ w.length * d + g * w.canonicalEnd) =
          3 ^ w.length * w.canonicalStart +
            w.affineConst := by
      calc
        3 ^ w.length * w.canonicalStart +
              (3 ^ w.length * d + g * w.canonicalEnd)
            =
          (3 ^ w.length + g) * w.canonicalEnd := by
            rw [hend]
            ring
        _ = 2 ^ w.twoSteps * w.canonicalEnd := by
            rw [← htwo]
        _ = 3 ^ w.length * w.canonicalStart +
              w.affineConst := hreal
    exact (Nat.add_left_cancel hcancel).symm
  /-
  g > 0 かつ canonicalEnd > 0 なので、
  分解式の第二項は真に正。
  -/
  have hgzPos : 0 < g * w.canonicalEnd :=
    Nat.mul_pos hg hendPos
  /-
  よって affineConst は
    3^length * d
  より真に大きい。
  -/
  have hlow :
      3 ^ w.length * d < w.affineConst := by
    rw [hid]
    omega
  /-
  first crossing に対する affine constant の sharp upper bound。
  -/
  have hB :
      w.affineConst ≤
        w.length * 3 ^ (w.length - 1) :=
    hF.affineConst_le_sharp
  /-
  上下の評価を合成する。
  -/
  have hchain :
      3 ^ w.length * d <
        w.length * 3 ^ (w.length - 1) :=
    lt_of_lt_of_le hlow hB
  /-
  first crossing は空語ではないので length > 0。
  length = r + 1 と書き直して共通因子 3^r を取り出す。
  -/
  have hlenPos :
      0 < w.length :=
    List.length_pos_of_ne_nil hF.nonempty
  obtain ⟨r, hr⟩ : ∃ r : ℕ, w.length = r + 1 :=
    ⟨w.length - 1, by omega⟩
  rw [hr] at hchain ⊢
  /-
  3^r は正なので、strict inequality から約分できる。
  -/
  have hpowPos : 0 < 3 ^ r :=
    Nat.pow_pos (by omega)
  have hscaled :
      3 ^ r * (3 * d) <
        3 ^ r * (r + 1) := by
    simpa [pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hchain
  exact (Nat.mul_lt_mul_left hpowPos).mp hscaled
namespace FirstCrossingData

/-- first crossingより後、adjacent endpointまでのactual suffix word。 -/
def lateSuffixWord
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) : Collatz.Word :=
  O.segment
    (R.startIndex + F.length)
    (R.length - F.length)

/-- adjacent wordをfirst-crossing prefixと残りsuffixへ分解する。 -/
theorem word_eq_crossing_append_lateSuffix
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    R.word =
      R.word.take F.length ++ F.lateSuffixWord := by
  have h :=
    R.word_eq_prefix_append_suffix F.le_adjacent
  simpa [lateSuffixWord, F.word_eq_segment] using h

/-- actual first crossingをcanonical replay座標で表す。 -/
def replayCoordinate
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    Word.ReplayCoordinate
      (R.word.take F.length)
      R.startValue
      F.endpointValue := by
  apply Word.ReplayCoordinate.ofRealization F.realizes
  exact O.value_odd _

/--
Baker型gap下界のもと、十分長いactual first crossingの
canonical replay quotientは0。
-/
theorem replayQuotient_eq_zero_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        N ≤ F.length →
          F.replayCoordinate.quotient = 0 := by
  obtain ⟨N, hN⟩ :=
    multiplicativeGap_gt_length_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hlen
  let w : Collatz.Word :=
    R.word.take F.length
  let C : Word.ReplayCoordinate
      w
      R.startValue
      F.endpointValue :=
    F.replayCoordinate
  let q : ℕ := C.quotient
  have hwordContracting : w.Contracting := by
    simpa [w] using F.crossing.terminalContracting
  have hstartCoord :
      R.startValue =
        w.canonicalStart +
          w.residueModulus * q := by
    simpa [q] using C.start_eq
  have hfinishCoord :
      F.endpointValue =
        w.canonicalEnd +
          2 * 3 ^ w.oddSteps * q := by
    simpa [q] using C.finish_eq
  have hposReplay :
      w.canonicalStart +
          w.residueModulus * q ≤
        w.canonicalEnd +
          2 * 3 ^ w.oddSteps * q := by
    calc
      w.canonicalStart +
            w.residueModulus * q
          = R.startValue := hstartCoord.symm
      _ ≤ F.endpointValue := F.start_le_endpoint
      _ =
          w.canonicalEnd +
            2 * 3 ^ w.oddSteps * q := hfinishCoord
  have hbalance :=
    Word.Contracting.replayGap_balance
      hwordContracting q
  change q = 0
  by_contra hq
  have hqPos : 0 < q :=
    Nat.pos_of_ne_zero hq
  have hcontractingGapPos :
      0 < w.contractingGap := by
    have hC := hwordContracting
    unfold Word.Contracting at hC
    unfold Word.contractingGap
    exact Nat.sub_pos_of_lt hC
  have hpenaltyPos :
      0 < 2 * w.contractingGap * q := by
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) hcontractingGapPos)
      hqPos
  have hcanonicalPos :
      w.canonicalStart < w.canonicalEnd := by
    omega
  have hpenaltyLe :
      2 * w.contractingGap * q ≤
        w.canonicalEnd - w.canonicalStart := by
    omega
  have hqOne : 1 ≤ q := by
    omega
  have hpenalty :
      2 * w.contractingGap ≤
        2 * w.contractingGap * q := by
    have h :=
      Nat.mul_le_mul_left
        (2 * w.contractingGap) hqOne
    simpa using h
  have htwoGapLe :
      2 * w.contractingGap ≤
        w.canonicalEnd - w.canonicalStart :=
    le_trans hpenalty hpenaltyLe
  have hgapDef :
      w.contractingGap =
        F.multiplicativeGap := by
    simp [
      w,
      Word.contractingGap,
      multiplicativeGap,
      totalExponent,
      F.oddSteps_word
    ]
  have hsharp :
      3 * (w.canonicalEnd - w.canonicalStart) <
        F.length := by
    have h :=
      firstCrossing_three_mul_canonicalGap_lt_length
        F.crossing hcanonicalPos
    simpa [w, F.word_length] using h
  have hlarge :
      F.length < F.multiplicativeGap :=
    hN O R F hlen
  rw [hgapDef] at htwoGapLe
  omega

/-- 十分長いactual first crossingはcanonical startそのものから始まる。 -/
theorem startValue_eq_canonicalStart_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        N ≤ F.length →
          R.startValue =
            Word.canonicalStart (R.word.take F.length) := by
  obtain ⟨N, hN⟩ :=
    replayQuotient_eq_zero_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hlen
  exact
    F.replayCoordinate.start_eq_canonical_of_quotient_eq_zero
      (hN O R F hlen)

/--
first crossingのstartがcanonicalなら、Late suffix全体の
aggregate cylinder digitは0。
-/
theorem lateSuffix_extensionDigit_eq_zero_of_start_canonical
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R)
    (_hLate : F.IsLate)
    (hstart :
      R.startValue =
        Word.canonicalStart (R.word.take F.length)) :
    Word.extensionDigit
      (R.word.take F.length)
      F.lateSuffixWord = 0 := by
  let A : Collatz.Word := R.word.take F.length
  let C : Collatz.Word := F.lateSuffixWord
  have hword :
      R.word = A ++ C := by
    simpa [A, C] using F.word_eq_crossing_append_lateSuffix
  have hvalid :
      Word.Valid (A ++ C) := by
    rw [← hword]
    exact R.word_valid
  have hAne : A ≠ [] := by
    simpa [A] using F.crossing.nonempty
  have hstartA :
      R.startValue = Word.canonicalStart A := by
    simpa [A] using hstart
  have hstartLtA :
      R.startValue < Word.residueModulus A := by
    rw [hstartA]
    exact Word.canonicalStart_lt_modulus A
  have hmodulus :
      Word.residueModulus (A ++ C) =
        Word.residueModulus A * 2 ^ Word.twoSteps C := by
    simp [Word.residueModulus, Word.twoSteps_append, pow_add]
    ac_rfl
  have hpowOne :
      1 ≤ 2 ^ Word.twoSteps C := by
    have hpowPos :
        0 < 2 ^ Word.twoSteps C :=
      Nat.pow_pos (by omega)
    omega
  have hmodLe :
      Word.residueModulus A ≤
        Word.residueModulus (A ++ C) := by
    rw [hmodulus]
    have h :=
      Nat.mul_le_mul_left
        (Word.residueModulus A) hpowOne
    simpa using h
  have hstartLtWhole :
      R.startValue <
        Word.residueModulus (A ++ C) :=
    lt_of_lt_of_le hstartLtA hmodLe
  have hreal :
      Word.Realizes
        (A ++ C)
        R.startValue
        R.nextValue := by
    rw [← hword]
    exact R.realizes
  have hnextOdd : Odd R.nextValue := by
    unfold State.nextValue
    exact O.value_odd _
  have hwholeCanonical :
      R.startValue =
        Word.canonicalStart (A ++ C) := by
    exact
      Word.Realizes.eq_canonicalStart_of_lt_modulus
        hreal hnextOdd hstartLtWhole
  unfold Word.extensionDigit
  rw [← hwholeCanonical]
  exact Nat.div_eq_of_lt hstartLtA


/--
Baker型gap下界のもと、十分長いLate項では
first-crossing prefixから残りsuffixへのaggregate digitが0。
-/
theorem lateSuffix_extensionDigit_eq_zero_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        F.IsLate →
        N ≤ F.length →
          Word.extensionDigit
            (R.word.take F.length)
            F.lateSuffixWord = 0 := by
  obtain ⟨N, hN⟩ :=
    startValue_eq_canonicalStart_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hLate hlen
  exact
    lateSuffix_extensionDigit_eq_zero_of_start_canonical
      F hLate (hN O R F hlen)


/--
Baker型gap下界のもと、十分長いLate項では
残りsuffixを一文字ずつ伸ばすすべてのcylinder digitが0。
-/
theorem lateSuffix_allExtensionDigitsZero_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        F.IsLate →
        N ≤ F.length →
          Word.AllExtensionDigitsZero
            (R.word.take F.length)
            F.lateSuffixWord := by
  obtain ⟨N, hN⟩ :=
    lateSuffix_extensionDigit_eq_zero_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hLate hlen
  let A : Collatz.Word := R.word.take F.length
  let C : Collatz.Word := F.lateSuffixWord
  have hword :
      R.word = A ++ C := by
    simpa [A, C] using
      F.word_eq_crossing_append_lateSuffix
  have hvalid :
      Word.Valid (A ++ C) := by
    rw [← hword]
    exact R.word_valid
  have hAne : A ≠ [] := by
    simpa [A] using F.crossing.nonempty
  have hzero :
      Word.extensionDigit A C = 0 := by
    simpa [A, C] using
      hN O R F hLate hlen
  exact
    allExtensionDigitsZero_of_extensionDigit_eq_zero
      hvalid hAne hzero

end FirstCrossingData
end AdjacentReturn
end Collatz
