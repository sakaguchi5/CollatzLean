import CollatzLean.Collatz3.Semantics.OrbitFate
import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences

/-!
# Collatz3: 三つの軌道終局型から finite arithmetic への bridge

`OrbitFate` の三つの薄い意味論的枝を pure / canonical data の定義へ埋め込まず、
既存の finite arithmetic へ derived theorem として接続する。

* 第1枝 `HitsOne`:
  開始値が `1` でなければ唯一の first-hit word を持ち、`y=1` の affine equation と
  canonical coordinates `R=x`, `Y=1`, `Q=1-x` を得る。
* 第2枝 `HasNontrivialRepeat`:
  到達可能な非自明 primitive return を持ち、`B=(2^H-3^p)x` と canonical gap multiple を得る。
* 第3枝 `DivergesToInfinity`:
  任意に遠い actual future minimum で exponent `1` の一段 run を得る。

真の `RecordFerrers` はこの三分類を field に持たず、後段でこの bridge を利用する。
-/

namespace Collatz3
namespace OrbitFate

/--
第1枝の finite arithmetic packet。
開始値が `1` でない場合、first-hit word 上で affine equation と canonical coordinates が同時に閉じる。
-/
theorem hitsOne_firstHit_affine_canonical
    (O : OddOrbit)
    (hHit : O.HitsOne)
    (hStart : O.value 0 ≠ 1) :
    ∃ w : Word,
      FirstHitsOne w (O.value 0) ∧
      2 ^ Word.twoSteps w =
        3 ^ Word.oddSteps w * O.value 0 + Word.affineConst w ∧
      Word.canonicalStart w = O.value 0 ∧
      Word.canonicalEnd w = 1 ∧
      Word.canonicalGap w = (1 : ℤ) - (O.value 0 : ℤ) := by
  have hReach : ReachesOne (O.value 0) :=
    (OddOrbit.hitsOne_iff_reachesOne O).1 hHit
  rcases ReachesOne.exists_firstHitsOne_of_ne_one hStart hReach with
    ⟨w, hw⟩
  have hAffine := ReachOne.affineEquation hw.endsAtOne
  have hCanonical := ReachOne.firstHit_canonicalCoordinates hw
  exact
    ⟨w, hw, hAffine,
      hCanonical.1,
      hCanonical.2.1,
      hCanonical.2.2⟩

/--
第1枝を開始値 `1` の自明な場合も含めて全体化する。
開始値が既に `1` ならそこで自明周期に入っており、そうでなければ first-hit arithmetic packet を持つ。
-/
theorem hitsOne_start_eq_one_or_firstHit_affine_canonical
    (O : OddOrbit)
    (hHit : O.HitsOne) :
    O.value 0 = 1 ∨
      ∃ w : Word,
        FirstHitsOne w (O.value 0) ∧
        2 ^ Word.twoSteps w =
          3 ^ Word.oddSteps w * O.value 0 + Word.affineConst w ∧
        Word.canonicalStart w = O.value 0 ∧
        Word.canonicalEnd w = 1 ∧
        Word.canonicalGap w = (1 : ℤ) - (O.value 0 : ℤ) := by
  by_cases hStart : O.value 0 = 1
  · exact Or.inl hStart
  · exact Or.inr (hitsOne_firstHit_affine_canonical O hHit hStart)

/--
第2枝の finite arithmetic packet。
非自明 repeated state を primitive return に正規化し、周期 affine equation の signed 形と
canonical gap multiple を同時に得る。
-/
theorem nontrivialRepeat_periodic_affine_canonical
    (O : OddOrbit)
    (hRepeat : O.HasNontrivialRepeat) :
    ∃ i : ℕ, ∃ w : Word,
      Reaches (O.value 0) (O.value i) ∧
      IsNontrivialPeriodicOrbit w (O.value i) ∧
      (Word.affineConst w : ℤ) =
        Word.signedScaleGap w * (O.value i : ℤ) ∧
      ∃ k : ℕ,
        Word.canonicalGap w =
          2 * (k : ℤ) * Word.signedScaleGap w := by
  rcases OddOrbit.exists_eventual_nontrivialPeriodicOrbit_of_repeat O hRepeat with
    ⟨i, w, hReach, hPeriodic⟩
  have hAffine :=
    OrbitReturn.affineConst_int_eq_scaleGap_mul_start
      (PrimitiveReturn.returnsTo hPeriodic.1)
  rcases OrbitReturn.nontrivial_canonicalGap_is_evenScaleGapMultiple hPeriodic with
    ⟨k, hk⟩
  exact ⟨i, w, hReach, hPeriodic, hAffine, k, hk⟩

/--
第3枝では、任意の指定時刻より後に値 `>1` の future minimum があり、
そこで exponent `1` の actual one-step run `[1]` が始まる。
-/
theorem diverges_exists_late_exponent_one_run
    (O : OddOrbit)
    (hDiv : O.DivergesToInfinity)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      Runs [1] (O.value n) (O.value (n + 1)) ∧
      2 * O.value (n + 1) = 3 * O.value n + 1 := by
  rcases O.exists_futureMinimum_exponent_eq_one_after_of_diverges hDiv start with
    ⟨n, hStart, hMin, hOneLt, hExp⟩
  have hRun := O.runsSegment n 1
  have hRunOne : Runs [1] (O.value n) (O.value (n + 1)) := by
    simpa [OddOrbit.segmentWord, hExp] using hRun
  have hStep := O.step n
  rw [hExp] at hStep
  have hAffine : 2 * O.value (n + 1) = 3 * O.value n + 1 := by
    simpa using hStep.equation
  exact ⟨n, hStart, hMin, hOneLt, hExp, hRunOne, hAffine⟩

end OrbitFate
end Collatz3
