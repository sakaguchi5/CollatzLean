import CollatzLean.Collatz2.Global.RightBranchFirstCrossing
import CollatzLean.Collatz2.Arithmetic.TwoThreeSmallGap
import Mathlib.Tactic.Linarith

/-!
# Collatz2: right branch を q=0 へ圧縮する

`RightBranchFirstCrossing` で得た

  6*r + 6*G*q < p

と外部整数論 interface `TwoThreeSmallGapExclusion` を接続する。

`q>0` なら `r>0` と合わせて

  6*G + 6 < p

が出る。一方 terminal contracting から

  G = 2^H - 3^p > 0

なので、外部 small-gap exclusion に反する。
従って replay quotient は exact に `q=0`。

このファイル自身は axiom を import しない。
`TwoThreeSmallGapExclusion` を仮定として受け取る条件付き Collatz theorem だけを置く。
-/

namespace Collatz2
namespace Word
namespace FirstCrossing

/--
positive actual FirstCrossing で replay quotient が正なら、Collatz 固有情報を捨てて
純粋な two-three small-gap packet

  G > 0
  2^H = 3^p + G
  6*G + 6 < p

へ射影できる。
-/
theorem positive_replay_forces_twoThreeSmallGap
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y)
    (hq :
      0 < (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient) :
    0 < (AffineTransfer.ofWord w).centerGap ∧
      2 ^ twoSteps w =
        3 ^ oddSteps w + (AffineTransfer.ofWord w).centerGap ∧
      6 * (AffineTransfer.ofWord w).centerGap + 6 < oddSteps w := by
  let T := AffineTransfer.ofWord w
  let R : ReplayCoordinate w X Y :=
    ReplayCoordinate.ofRuns hrun hF.nonempty
  obtain ⟨r, hrPos, _hActual, hbound⟩ :=
    hF.exists_actualHalfGap_replay_bound hrun hXY
  have hqR : 0 < R.quotient := by
    simpa [R] using hq
  have hneg : T.determinant < 0 := by
    simpa [T, AffineTransfer.NegativeDeterminant] using
      hF.terminalNegative
  have hGpos : 0 < T.centerGap :=
    T.centerGap_pos_of_negative hneg
  have hCA : T.oddCoeff ≤ T.twoCoeff := by
    unfold AffineTransfer.determinant at hneg
    omega
  have hgapCoeff :
      T.centerGap + T.oddCoeff = T.twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hCA
  have hpower :
      2 ^ twoSteps w =
        3 ^ oddSteps w + T.centerGap := by
    calc
      2 ^ twoSteps w = T.twoCoeff := by rfl
      _ = T.centerGap + T.oddCoeff := hgapCoeff.symm
      _ = 3 ^ oddSteps w + T.centerGap := by
        simp [T, Nat.add_comm]
  change
    6 * r + 6 * T.centerGap * R.quotient < oddSteps w
      at hbound
  have hsmall :
      6 * T.centerGap + 6 < oddSteps w := by
    nlinarith
  exact ⟨by simpa [T] using hGpos,
    by simpa [T] using hpower,
    by simpa [T] using hsmall⟩

/--
外部 small-gap exclusion の下では `q>0` branch は存在しない。
-/
theorem not_positive_replayQuotient_of_twoThreeSmallGapExclusion
    (hGap : TwoThreeSmallGapExclusion)
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    ¬ 0 <
      (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient := by
  intro hq
  obtain ⟨hGpos, hpower, hsmall⟩ :=
    hF.positive_replay_forces_twoThreeSmallGap hrun hXY hq
  exact
    hGap
      (twoSteps w)
      (oddSteps w)
      (AffineTransfer.ofWord w).centerGap
      hGpos
      hpower
      hsmall

/--
外部 small-gap exclusion の下では、positive actual FirstCrossing の replay quotient は0。
-/
theorem replayQuotient_eq_zero_of_twoThreeSmallGapExclusion
    (hGap : TwoThreeSmallGapExclusion)
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient = 0 := by
  by_contra hne
  have hq :
      0 < (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient :=
    Nat.pos_of_ne_zero hne
  exact
    hF.not_positive_replayQuotient_of_twoThreeSmallGapExclusion
      hGap hrun hXY hq

/--
`q=0` により actual start/end は canonical start/end そのものになる。
-/
theorem actual_eq_canonical_of_twoThreeSmallGapExclusion
    (hGap : TwoThreeSmallGapExclusion)
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    X = canonicalStart w ∧
      Y = canonicalEnd w := by
  let R : ReplayCoordinate w X Y :=
    ReplayCoordinate.ofRuns hrun hF.nonempty
  have hq : R.quotient = 0 := by
    dsimp [R]
    exact
      hF.replayQuotient_eq_zero_of_twoThreeSmallGapExclusion
        hGap hrun hXY
  exact
    ⟨R.start_eq_canonical_of_quotient_eq_zero hq,
      R.finish_eq_canonical_of_quotient_eq_zero hq⟩

/--
外部 small-gap exclusion の下では、positive actual FirstCrossing は canonical-positive。
-/
theorem canonical_positive_of_twoThreeSmallGapExclusion
    (hGap : TwoThreeSmallGapExclusion)
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    canonicalStart w < canonicalEnd w := by
  obtain ⟨hX, hY⟩ :=
    hF.actual_eq_canonical_of_twoThreeSmallGapExclusion
      hGap hrun hXY
  calc
    canonicalStart w = X := hX.symm
    _ < Y := hXY
    _ = canonicalEnd w := hY

end FirstCrossing
end Word

namespace OddOrbit

/--
`¬ ForeverExpanding` な unbounded minimum-tail は、外部 small-gap exclusion の下で
canonical positive FirstCrossing を有限に含む。

actual run は q=0 により canonical run と exact に一致する。
-/
theorem exists_canonicalPositiveFirstCrossing_of_not_foreverExpanding
    (hGap : TwoThreeSmallGapExclusion)
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hNot :
      ¬ Word.NestedSurvivalChain.ForeverExpanding
          O.toNestedSurvivalChain) :
    ∃ w : Word,
      Word.Valid w ∧
        Word.FirstCrossing w ∧
        Runs w (Word.canonicalStart w) (Word.canonicalEnd w) ∧
        O.globalMinimumValue = Word.canonicalStart w ∧
        Word.canonicalStart w < Word.canonicalEnd w := by
  obtain ⟨w, y, hF, hrun, hXY⟩ :=
    O.exists_actualPositiveFirstCrossing_of_not_foreverExpanding
      hU hNot
  obtain ⟨hX, hY⟩ :=
    hF.actual_eq_canonical_of_twoThreeSmallGapExclusion
      hGap hrun hXY
  have hcanonicalRun :
      Runs w (Word.canonicalStart w) (Word.canonicalEnd w) := by
    rw [← hX, ← hY]
    exact hrun
  have hcanonicalPos :
      Word.canonicalStart w < Word.canonicalEnd w := by
    calc
      Word.canonicalStart w = O.globalMinimumValue := hX.symm
      _ < y := hXY
      _ = Word.canonicalEnd w := hY
  exact
    ⟨w, hrun.valid, hF, hcanonicalRun, hX, hcanonicalPos⟩

end OddOrbit

/--
外部 small-gap exclusion を仮定すると、非有界反例は

* minimum-tail が forever expanding
* canonical positive FirstCrossing を一つ有限に含む

の二つに圧縮される。
右側では replay quotient は既に `q=0` である。
-/
theorem hasUnboundedOddOrbit_to_foreverExpanding_or_canonicalPositiveFirstCrossing
    (hGap : TwoThreeSmallGapExclusion) :
    HasUnboundedOddOrbit →
      ∃ O : OddOrbit,
        O.Unbounded ∧
          (
            Word.NestedSurvivalChain.ForeverExpanding
              O.toNestedSurvivalChain
            ∨
            ∃ w : Word,
              Word.Valid w ∧
                Word.FirstCrossing w ∧
                Runs w (Word.canonicalStart w) (Word.canonicalEnd w) ∧
                O.globalMinimumValue = Word.canonicalStart w ∧
                Word.canonicalStart w < Word.canonicalEnd w
          ) := by
  classical
  rintro ⟨O, hU⟩
  refine ⟨O, hU, ?_⟩
  by_cases hE :
      Word.NestedSurvivalChain.ForeverExpanding
        O.toNestedSurvivalChain
  · exact Or.inl hE
  · exact Or.inr
      (O.exists_canonicalPositiveFirstCrossing_of_not_foreverExpanding
        hGap hU hE)

end Collatz2
