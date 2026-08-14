import CollatzLean.Collatz2.Global.OddOrbitSurvivalBridge
import CollatzLean.Collatz2.Local.TranslationDeterminant
import CollatzLean.Collatz2.Canonical.ReplayExtremality

/-!
# Collatz2: right-branch reduction to a finite positive FirstCrossing obstruction

`hasUnboundedOddOrbit_to_strongInfiniteSurvivalDichotomy` の右枝を生成する
`¬ ForeverExpanding` から、actual positive `FirstCrossing` を有限に切り出す。

右枝そのものには現時点では `¬ ForeverExpanding` が明示保存されていないため、
このファイルでは既存 theorem statement を変更せず、右枝を生成する exact condition
`¬ ForeverExpanding` を入力にする。

さらに positive FirstCrossing に対して

* actual half-gap の prefix-determinant budget
* replay quotient による canonical/actual half-gap の exact 差
* `6*r + 6*G*q < p`

を導く。ここで

  `G = 2^H - 3^p = centerGap(ofWord w)`

である。
-/

namespace Collatz2

namespace Runs

/--
同じ word・同じ start を持つ二つの normalized run の endpoint は一意。
-/
theorem end_eq_of_same_word_start
    {w : Word} {x y z : ℕ}
    (hy : Runs w x y)
    (hz : Runs w x z) :
    y = z := by
  have hyEq := (Word.realizes_iff w x y).1 hy.realizes
  have hzEq := (Word.realizes_iff w x z).1 hz.realizes
  have hmul :
      2 ^ Word.twoSteps w * y =
        2 ^ Word.twoSteps w * z := by
    calc
      2 ^ Word.twoSteps w * y
          = 3 ^ Word.oddSteps w * x + Word.affineConst w := hyEq
      _ = 2 ^ Word.twoSteps w * z := hzEq.symm
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      hmul

end Runs

namespace Word

/-- `residueModulus = 2 * twoCoeff` の word 版。 -/
theorem residueModulus_eq_two_mul_twoCoeff
    (w : Word) :
    residueModulus w =
      2 * (AffineTransfer.ofWord w).twoCoeff := by
  unfold residueModulus
  change 2 ^ (twoSteps w + 1) = 2 * 2 ^ twoSteps w
  rw [pow_succ]
  ring

/--
二つの odd boundary の strict gap は正の half-gap `r` を持つ。
-/
theorem exists_positive_halfGap_of_odd_lt
    {X Y : ℕ}
    (hX : Odd X)
    (hY : Odd Y)
    (hXY : X < Y) :
    ∃ r : ℕ,
      0 < r ∧ Y = X + 2 * r := by
  rcases hX with ⟨a, ha⟩
  rcases hY with ⟨b, hb⟩
  have hab : a < b := by
    omega
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  omega

namespace FirstCrossing

/--
positive actual FirstCrossing の half-gap `r` に対する sharp prefix budget。

`G = centerGap = 2^H - 3^p` とすると

  `3*G*Y + 6*r*3^p <= p*3^p`。
-/
theorem exists_actualHalfGap_and_budget
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    ∃ r : ℕ,
      0 < r ∧
      Y = X + 2 * r ∧
      3 * (AffineTransfer.ofWord w).centerGap * Y +
          6 * r * 3 ^ oddSteps w ≤
        oddSteps w * 3 ^ oddSteps w := by
  obtain ⟨r, hrPos, hY⟩ :=
    exists_positive_halfGap_of_odd_lt
      (hrun.start_odd_of_ne_nil hF.nonempty)
      (hrun.end_odd_of_ne_nil hF.nonempty)
      hXY
  let T := AffineTransfer.ofWord w
  have hneg : T.determinant < 0 := by
    simpa [T, AffineTransfer.NegativeDeterminant] using
      hF.terminalNegative
  have hCA : T.oddCoeff ≤ T.twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hgapCoeff :
      T.centerGap + T.oddCoeff = T.twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hreal :
      T.twoCoeff * Y = T.oddCoeff * X + T.translate := by
    simpa [T, Word.Realizes, AffineTransfer.Realizes] using
      hrun.realizes
  have hrealZ :
      (T.twoCoeff : ℤ) * (Y : ℤ) =
        (T.oddCoeff : ℤ) * (X : ℤ) + (T.translate : ℤ) := by
    exact_mod_cast hreal
  have hgapCoeffZ :
      (T.centerGap : ℤ) + (T.oddCoeff : ℤ) =
        (T.twoCoeff : ℤ) := by
    exact_mod_cast hgapCoeff
  have hYZ :
      (Y : ℤ) = (X : ℤ) + 2 * (r : ℤ) := by
    exact_mod_cast hY
  have htranslateZ :
      (T.translate : ℤ) =
        (T.centerGap : ℤ) * (Y : ℤ) +
          (T.oddCoeff : ℤ) * (2 * (r : ℤ)) := by
    calc
      (T.translate : ℤ)
          = (T.twoCoeff : ℤ) * (Y : ℤ) -
              (T.oddCoeff : ℤ) * (X : ℤ) := by
                linarith
      _ =
          ((T.centerGap : ℤ) + (T.oddCoeff : ℤ)) * (Y : ℤ) -
            (T.oddCoeff : ℤ) * (X : ℤ) := by
              rw [hgapCoeffZ]
      _ =
          (T.centerGap : ℤ) * (Y : ℤ) +
            (T.oddCoeff : ℤ) * ((Y : ℤ) - (X : ℤ)) := by
              ring
      _ =
          (T.centerGap : ℤ) * (Y : ℤ) +
            (T.oddCoeff : ℤ) * (2 * (r : ℤ)) := by
              rw [hYZ]
              ring
  have htranslate :
      T.translate =
        T.centerGap * Y + T.oddCoeff * (2 * r) := by
    exact_mod_cast htranslateZ
  have hbudget :
      3 * T.translate ≤ oddSteps w * T.oddCoeff := by
    simpa [T] using
      hF.three_mul_affineConst_le_oddSteps_mul_threePow
  refine ⟨r, hrPos, hY, ?_⟩
  calc
    3 * (AffineTransfer.ofWord w).centerGap * Y +
          6 * r * 3 ^ oddSteps w
        = 3 * T.translate := by
            rw [htranslate]
            dsimp [T]
            ring
    _ ≤ oddSteps w * T.oddCoeff := hbudget
    _ = oddSteps w * 3 ^ oddSteps w := by
          rfl

/--
positive actual FirstCrossing の half-gap は必ず `6*r < p`。
-/
theorem exists_actualHalfGap_six_lt_oddSteps
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    ∃ r : ℕ,
      0 < r ∧
      Y = X + 2 * r ∧
      6 * r < oddSteps w := by
  obtain ⟨r, hrPos, hY, hbudget⟩ :=
    hF.exists_actualHalfGap_and_budget hrun hXY
  let T := AffineTransfer.ofWord w
  have hneg : T.determinant < 0 := by
    simpa [T, AffineTransfer.NegativeDeterminant] using
      hF.terminalNegative
  have hGpos : 0 < T.centerGap :=
    T.centerGap_pos_of_negative hneg
  have hYpos : 0 < Y := by
    rcases hrun.end_odd_of_ne_nil hF.nonempty with ⟨k, hk⟩
    omega
  have hGpos' :
      0 < (AffineTransfer.ofWord w).centerGap := by
    simpa [T] using hGpos
  have hstrictMul :
      (6 * r) * 3 ^ oddSteps w <
        oddSteps w * 3 ^ oddSteps w := by
    have hfirstPos :
        0 < 3 * (AffineTransfer.ofWord w).centerGap * Y := by
      positivity
    omega
  have hsix : 6 * r < oddSteps w := by
    by_contra hnot
    have hle : oddSteps w ≤ 6 * r := Nat.le_of_not_gt hnot
    have hmul :
        oddSteps w * 3 ^ oddSteps w ≤
          (6 * r) * 3 ^ oddSteps w :=
      Nat.mul_le_mul_right (3 ^ oddSteps w) hle
    exact (Nat.not_lt_of_ge hmul) hstrictMul
  exact ⟨r, hrPos, hY, hsix⟩

end FirstCrossing

namespace ReplayCoordinate

/--
replay coordinate の canonical/actual half-gap exact identity。

actual gap が `2*r`、canonical gap が `2*n` なら

  `n = r + G*q`

である。ここで `G = centerGap = 2^H - 3^p`、`q = quotient`。
-/
theorem canonicalHalfGap_eq_actualHalfGap_add_centerGap_mul_quotient
    {w : Word} {X Y r n : ℕ}
    (C : ReplayCoordinate w X Y)
    (hC : Contracting w)
    (hActual : Y = X + 2 * r)
    (hCanonical : canonicalEnd w = canonicalStart w + 2 * n) :
    n =
      r + (AffineTransfer.ofWord w).centerGap * C.quotient := by
  let T := AffineTransfer.ofWord w
  let q := C.quotient
  have hneg : T.determinant < 0 := by
    simpa [T, Contracting, AffineTransfer.NegativeDeterminant] using hC
  have hCA : T.oddCoeff ≤ T.twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hgapCoeff :
      T.centerGap + T.oddCoeff = T.twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hstart :
      X = canonicalStart w + 2 * T.twoCoeff * q := by
    calc
      X = canonicalStart w + residueModulus w * C.quotient := C.start_eq
      _ = canonicalStart w +
          (2 * (AffineTransfer.ofWord w).twoCoeff) * C.quotient := by
            rw [residueModulus_eq_two_mul_twoCoeff]
      _ = canonicalStart w + 2 * T.twoCoeff * q := by
            simp [T, q, mul_assoc]
  have hfinish :
      Y = canonicalEnd w + 2 * T.oddCoeff * q := by
    simpa [T, q, mul_assoc] using C.finish_eq
  have hEq :
      canonicalStart w + 2 * n + 2 * T.oddCoeff * q =
        canonicalStart w + 2 * T.twoCoeff * q + 2 * r := by
    calc
      canonicalStart w + 2 * n + 2 * T.oddCoeff * q
          = canonicalEnd w + 2 * T.oddCoeff * q := by
              rw [hCanonical]
      _ = Y := hfinish.symm
      _ = X + 2 * r := hActual
      _ = canonicalStart w + 2 * T.twoCoeff * q + 2 * r := by
              rw [hstart]
  have hEq2 :
      2 * n + 2 * T.oddCoeff * q =
        2 * T.twoCoeff * q + 2 * r := by
    omega
  have hTwice :
      2 * (n + T.oddCoeff * q) =
        2 * (T.twoCoeff * q + r) := by
    calc
      2 * (n + T.oddCoeff * q)
          = 2 * n + 2 * T.oddCoeff * q := by ring
      _ = 2 * T.twoCoeff * q + 2 * r := hEq2
      _ = 2 * (T.twoCoeff * q + r) := by ring
  have hbase :
      n + T.oddCoeff * q = T.twoCoeff * q + r :=
    Nat.mul_left_cancel (by omega : 0 < (2 : ℕ)) hTwice
  have hbase' :
      n + T.oddCoeff * q =
        (T.centerGap + T.oddCoeff) * q + r := by
    simpa [hgapCoeff] using hbase
  have hcancel :
      T.oddCoeff * q + n =
        T.oddCoeff * q + (r + T.centerGap * q) := by
    calc
      T.oddCoeff * q + n
          = n + T.oddCoeff * q := by ring
      _ = (T.centerGap + T.oddCoeff) * q + r := hbase'
      _ = T.oddCoeff * q + (r + T.centerGap * q) := by ring
  have hn : n = r + T.centerGap * q :=
    Nat.add_left_cancel hcancel
  simpa [T, q] using hn

end ReplayCoordinate

namespace FirstCrossing

/--
positive actual FirstCrossing の replay quotient を含む最終 half-gap bound。

actual half-gap を `r`、`G=centerGap`、replay quotient を `q` とすると

  `6*r + 6*G*q < p`。
-/
theorem exists_actualHalfGap_replay_bound
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    ∃ r : ℕ,
      0 < r ∧
      Y = X + 2 * r ∧
      6 * r +
          6 * (AffineTransfer.ofWord w).centerGap *
            (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient <
        oddSteps w := by
  obtain ⟨r, hrPos, hActual, _hActualBudget⟩ :=
    hF.exists_actualHalfGap_and_budget hrun hXY
  have hvalid : Valid w := hrun.valid
  have hC : Contracting w := hF.terminalContracting
  have hCanonicalPos : canonicalStart w < canonicalEnd w :=
    hrun.canonical_positive_of_contracting_positive
      hF.nonempty hC hXY
  have hCanonicalRun :
      Runs w (canonicalStart w) (canonicalEnd w) :=
    canonicalRuns hvalid
  obtain ⟨n, _hnPos, hCanonical, hCanonicalBudget⟩ :=
    hF.exists_actualHalfGap_and_budget
      hCanonicalRun hCanonicalPos
  let R : ReplayCoordinate w X Y :=
    ReplayCoordinate.ofRuns hrun hF.nonempty
  have hnEq :
      n = r + (AffineTransfer.ofWord w).centerGap * R.quotient :=
    R.canonicalHalfGap_eq_actualHalfGap_add_centerGap_mul_quotient
      hC hActual hCanonical
  let T := AffineTransfer.ofWord w
  have hneg : T.determinant < 0 := by
    simpa [T, Contracting, AffineTransfer.NegativeDeterminant] using hC
  have hGpos : 0 < T.centerGap :=
    T.centerGap_pos_of_negative hneg
  have hEndPos : 0 < canonicalEnd w :=
    canonicalEnd_pos w
  have hGpos' :
      0 < (AffineTransfer.ofWord w).centerGap := by
    simpa [T] using hGpos
  have hfirstPos :
      0 <
        3 * (AffineTransfer.ofWord w).centerGap *
          canonicalEnd w := by
    positivity
  have hstrictMul :
      (6 * n) * 3 ^ oddSteps w <
        oddSteps w * 3 ^ oddSteps w := by
    omega
  have hsixN : 6 * n < oddSteps w := by
    by_contra hnot
    have hle : oddSteps w ≤ 6 * n := Nat.le_of_not_gt hnot
    have hmul :
        oddSteps w * 3 ^ oddSteps w ≤
          (6 * n) * 3 ^ oddSteps w :=
      Nat.mul_le_mul_right (3 ^ oddSteps w) hle
    exact (Nat.not_lt_of_ge hmul) hstrictMul
  refine ⟨r, hrPos, hActual, ?_⟩
  calc
    6 * r +
          6 * (AffineTransfer.ofWord w).centerGap * R.quotient
        = 6 * n := by
            rw [hnEq]
            ring
    _ < oddSteps w := hsixN

end FirstCrossing
end Word

namespace OddOrbit

/--
`¬ ForeverExpanding` な unbounded minimum-tail から、actual positive FirstCrossing を
有限に切り出す。

これは現在の strong dichotomy の右枝を生成する exact condition を使う theorem であり、
既存右枝 statement に `¬ ForeverExpanding` を追加する変更は行わない。
-/
theorem exists_actualPositiveFirstCrossing_of_not_foreverExpanding
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hNot :
      ¬ Word.NestedSurvivalChain.ForeverExpanding
          O.toNestedSurvivalChain) :
    ∃ w : Word,
      ∃ y : ℕ,
        Word.FirstCrossing w ∧
          Runs w O.globalMinimumValue y ∧
          O.globalMinimumValue < y := by
  classical
  have hNot' :
      ¬ ∀ n : ℕ, Word.Expanding (O.minimumTailWord n) := by
    simpa [Word.NestedSurvivalChain.ForeverExpanding,
      OddOrbit.toNestedSurvivalChain] using hNot
  have hex :
      ∃ m : ℕ, ¬ Word.Expanding (O.minimumTailWord m) := by
    simpa using hNot'
  obtain ⟨m, hmNotExpanding⟩ := hex
  have hmContracting :
      Word.Contracting (O.minimumTailWord m) := by
    rcases
        Word.expanding_or_contracting_of_valid_nonempty
          (O.minimumTailWord_valid m)
          (O.minimumTailWord_nonempty m) with hExp | hCon
    · exact False.elim (hmNotExpanding hExp)
    · exact hCon
  obtain ⟨p, hpLe, hF⟩ :=
    Word.exists_firstCrossing_of_contracting
      (O.minimumTailWord_valid m)
      (O.minimumTailWord_nonempty m)
      hmContracting
  have hfull :
      Runs
        ((O.minimumTailWord m).take p ++
          (O.minimumTailWord m).drop p)
        O.globalMinimumValue
        (O.minimumTailEndpoint m) := by
    rw [List.take_append_drop]
    exact O.runs_minimumTail m
  obtain ⟨y, hrun, _hsuffix⟩ := Runs.split_append hfull
  have hxle : O.globalMinimumValue ≤ y := by
    exact
      O.minimumTail_allPrefixesSurvive m
        ((O.minimumTailWord m).take p)
        ((O.minimumTailWord m).drop p)
        (List.take_append_drop p (O.minimumTailWord m))
        y hrun
  have hpPos : 0 < p := by
    have hlenPos :
        0 < ((O.minimumTailWord m).take p).length :=
      List.length_pos_iff.mpr hF.nonempty
    rw [List.length_take_of_le hpLe] at hlenPos
    exact hlenPos
  let i := O.globalMinimumIndex
  have hpLeSegment : p ≤ m + 1 := by
    have hlen : (O.minimumTailWord m).length = m + 1 := by
      unfold minimumTailWord
      exact O.segment_length O.globalMinimumIndex (m + 1)
    rw [hlen] at hpLe
    exact hpLe
  have hwordSegment :
      (O.minimumTailWord m).take p = O.segment i p := by
    unfold minimumTailWord
    dsimp [i]
    exact O.segment_take_of_le hpLeSegment
  have hsegmentRun :
      Runs ((O.minimumTailWord m).take p)
        O.globalMinimumValue
        (O.value (i + p)) := by
    rw [hwordSegment]
    dsimp [i]
    simpa [O.value_globalMinimumIndex] using
      O.runsSegment O.globalMinimumIndex p
  have hyOrbit : y = O.value (i + p) :=
    hrun.end_eq_of_same_word_start hsegmentRun
  have hyNe : y ≠ O.globalMinimumValue := by
    intro hyEq
    have hvalues : O.value i = O.value (i + p) := by
      dsimp [i]
      rw [O.value_globalMinimumIndex]
      rw [← hyEq, hyOrbit]
    have hindices : i = i + p :=
      O.value_injective_of_unbounded hU hvalues
    omega
  have hxy : O.globalMinimumValue < y := by
    omega
  exact
    ⟨(O.minimumTailWord m).take p, y, hF, hrun, hxy⟩

end OddOrbit

/--
非有界反例は、minimum-tail が forever expanding であるか、actual positive
FirstCrossing を一つ有限に含むかのどちらか。

既存 strong dichotomy の statement を変更せずに、右枝生成条件を有限 obstruction へ
射影する top-level corollary。
-/
theorem hasUnboundedOddOrbit_to_foreverExpanding_or_actualPositiveFirstCrossing :
    HasUnboundedOddOrbit →
      ∃ O : OddOrbit,
        O.Unbounded ∧
          (
            Word.NestedSurvivalChain.ForeverExpanding
              O.toNestedSurvivalChain
            ∨
            ∃ w : Word,
              ∃ y : ℕ,
                Word.FirstCrossing w ∧
                  Runs w O.globalMinimumValue y ∧
                  O.globalMinimumValue < y
          ) := by
  classical
  rintro ⟨O, hU⟩
  refine ⟨O, hU, ?_⟩
  by_cases hE :
      Word.NestedSurvivalChain.ForeverExpanding
        O.toNestedSurvivalChain
  · exact Or.inl hE
  · exact Or.inr
      (O.exists_actualPositiveFirstCrossing_of_not_foreverExpanding hU hE)

end Collatz2
