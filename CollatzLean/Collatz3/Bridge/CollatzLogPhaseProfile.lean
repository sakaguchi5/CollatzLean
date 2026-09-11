import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Semantics.FirstPassage
import CollatzLean.Collatz3.Experimental2.RotationPhase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual prefix の log₂ growth と critical profile

finite actual run の log telescope と、critical first-passage word から抽出した full profile を
exact に接続する。

proper cut `k` では

`profileFromWord w k = beattyIndex k - prefixTwoDepth w k`

であり、正規化 Beatty roof の mechanical phase を

`ρ(k) = k * log₂(3/2) - normalizeRoof beattyIndex k`

と読むと、actual prefix endpoint `z` に対して

`log₂ z - log₂ x = profile(k) + ρ(k) + correctionSum`

が exact に成り立つ。

従って actual logarithmic growth は

* 整数 profile height、
* `[0,1)` に入る pure mechanical phase、
* strict positive な Collatz `+1` correction の総和

へ分解される。

このファイルでは RecordFerrers / canonicalRecordLengths へはまだ進まない。
full profile と actual orbit の間の exact bridge だけを置く。
-/

namespace Collatz3

namespace Runs

/--
append された exponent word に沿う actual run は、append の境界で actual に分割できる。

`Runs.append` の逆向きに相当する derived theorem。
-/
theorem split_append
    {u v : Word}
    {x z : ℕ}
    (h : Runs (u ++ v) x z) :
    ∃ y : ℕ, Runs u x y ∧ Runs v y z := by
  induction u generalizing x z with
  | nil =>
      refine ⟨x, Runs.nil x, ?_⟩
      simpa using h
  | cons e u ih =>
      rcases Runs.exists_intermediate_of_cons h with
        ⟨m, hstep, htail⟩
      rcases ih htail with ⟨y, hu, hv⟩
      exact ⟨y, Runs.cons hstep hu, hv⟩

/--
任意の `take k` は actual prefix run として実現される。
同時に `drop k` は残りの actual suffix run になる。
-/
theorem exists_take_run
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (k : ℕ) :
    ∃ z : ℕ,
      Runs (w.take k) x z ∧
        Runs (w.drop k) z y := by
  have hSplit : Runs (w.take k ++ w.drop k) x y := by
    simpa using h
  exact Runs.split_append hSplit

end Runs

namespace Bridge

/--
正規化 Beatty roof の mechanical phase は常に非負。
-/
theorem normalizedBeattyLogPhase_nonneg
    (k : ℕ) :
    0 ≤ Experimental2.roofPhase
      (Experimental2.normalizeRoof Critical.beattyIndex)
      collatzLogRotation k := by
  have h :=
    normalizeBeatty_isLowerMechanical_logb_three_halves.phase_nonneg k
  simpa [collatzLogRotation] using h

/--
正規化 Beatty roof の mechanical phase は常に `1` 未満。
-/
theorem normalizedBeattyLogPhase_lt_one
    (k : ℕ) :
    Experimental2.roofPhase
      (Experimental2.normalizeRoof Critical.beattyIndex)
      collatzLogRotation k < 1 := by
  have h :=
    normalizeBeatty_isLowerMechanical_logb_three_halves.phase_lt_one k
  simpa [collatzLogRotation] using h

end Bridge

namespace Runs

/--
full critical first-passage word の proper cut `k` までを actual に走ったとき、
logarithmic growth は

`profile height + normalized Beatty phase + correction sum`

へ exact に分解される。

ここで prefix run 自身の exponent word は `w.take k` であるため、
その total two-depth は `prefixTwoDepth w k` と definitionally 一致する。
-/
theorem logGrowth_eq_profile_add_roofPhase_add_correctionSum
    {w : Word}
    {k : Fin (Word.oddSteps w)}
    {x z : ℕ}
    (h : Runs (w.take k.1) x z)
    (hFirst : Word.CriticalFirstPassage w) :
    Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) =
      (Critical.profileFromWord w k : ℝ) +
        Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          Bridge.collatzLogRotation k.1 +
        h.logCorrectionSum := by
  have hkLe : k.1 ≤ Word.oddSteps w :=
    Nat.le_of_lt k.2
  have hSteps :
      Word.oddSteps (w.take k.1) = k.1 := by
    have hkLen : k.1 ≤ w.length := by
      simpa [Word.oddSteps] using Nat.le_of_lt k.isLt
    simp [Word.oddSteps, hkLen]
  have hDepth :
      Word.twoSteps (w.take k.1) =
        Word.prefixTwoDepth w k.1 := by
    rfl
  have hProfileNat :
      Critical.profileFromWord w k +
          Word.prefixTwoDepth w k.1 =
        Critical.beattyIndex k.1 := by
    have hLe := hFirst.prefixDepth_le_beatty k.2
    unfold Critical.profileFromWord
    omega
  have hNormalizeNat :
      Critical.beattyIndex k.1 =
        k.1 +
          Experimental2.normalizeRoof Critical.beattyIndex k.1 := by
    have hLinear :=
      Bridge.beattyIndex_hasUnitCarry.eq_linear_add_normalizeRoof k.1
    simpa [Critical.beattyIndex_one] using hLinear
  have hProfileReal :
      (Critical.profileFromWord w k : ℝ) +
          (Word.prefixTwoDepth w k.1 : ℝ) =
        (Critical.beattyIndex k.1 : ℝ) := by
    exact_mod_cast hProfileNat
  have hNormalizeReal :
      (Critical.beattyIndex k.1 : ℝ) =
        (k.1 : ℝ) +
          (Experimental2.normalizeRoof Critical.beattyIndex k.1 : ℝ) := by
    exact_mod_cast hNormalizeNat
  have hRaw :=
    h.logb_end_eq_start_add_steps_sub_depth_add_correctionSum
  rw [hSteps, hDepth] at hRaw
  change
    Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) =
      (Critical.profileFromWord w k : ℝ) +
        ((k.1 : ℝ) * Bridge.collatzLogRotation -
          (Experimental2.normalizeRoof Critical.beattyIndex k.1 : ℝ)) +
        h.logCorrectionSum
  rw [Bridge.collatzLogRotation_eq_logb_three_sub_one]
  linarith [hRaw, hProfileReal, hNormalizeReal]

/--
proper cut までの actual logarithmic growth は profile height 以上。

mechanical phase と correction sum がともに非負であることだけを使う。
-/
theorem profile_le_logGrowth
    {w : Word}
    {k : Fin (Word.oddSteps w)}
    {x z : ℕ}
    (h : Runs (w.take k.1) x z)
    (hFirst : Word.CriticalFirstPassage w) :
    (Critical.profileFromWord w k : ℝ) ≤
      Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) := by
  have hEq :=
    h.logGrowth_eq_profile_add_roofPhase_add_correctionSum hFirst
  have hPhase := Bridge.normalizedBeattyLogPhase_nonneg k.1
  have hCorr := h.logCorrectionSum_nonneg
  linarith

/--
proper cut までの actual logarithmic growth は

`profile height + 1 + correction sum`

より strict に小さい。
-/
theorem logGrowth_lt_profile_add_one_add_correctionSum
    {w : Word}
    {k : Fin (Word.oddSteps w)}
    {x z : ℕ}
    (h : Runs (w.take k.1) x z)
    (hFirst : Word.CriticalFirstPassage w) :
    Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) <
      (Critical.profileFromWord w k : ℝ) + 1 +
        h.logCorrectionSum := by
  have hEq :=
    h.logGrowth_eq_profile_add_roofPhase_add_correctionSum hFirst
  have hPhase := Bridge.normalizedBeattyLogPhase_lt_one k.1
  linarith

/--
full word の全 step start が `X` 以上なら、`take k` で切った prefix も同じ下限を保つ。
-/
theorem AllStartsAtLeast.take
    {X : ℕ}
    {w : Word}
    {x : ℕ}
    (hAbove : AllStartsAtLeast X w x)
    (k : ℕ) :
    AllStartsAtLeast X (w.take k) x := by
  intro u v e a hTake hu
  apply hAbove
      (u := u)
      (v := v ++ w.drop k)
      (e := e)
      (a := a)
  · calc
      w = w.take k ++ w.drop k := by
        symm
        exact List.take_append_drop k w
      _ = (u ++ e :: v) ++ w.drop k := by
        rw [hTake]
      _ = u ++ e :: (v ++ w.drop k) := by
        simp [List.append_assoc]
  · exact hu

/--
proper prefix の全 step start が `X>0` 以上なら、actual log growth は

`profile(k) + 1 + k/(3 X ln 2)`

より strict に小さい。
-/
theorem logGrowth_lt_profile_add_one_add_uniformCorrection
    {X : ℕ}
    {w : Word}
    {k : Fin (Word.oddSteps w)}
    {x z : ℕ}
    (h : Runs (w.take k.1) x z)
    (hFirst : Word.CriticalFirstPassage w)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X (w.take k.1) x) :
    Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) <
      (Critical.profileFromWord w k : ℝ) + 1 +
        (k.1 : ℝ) /
          (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  have hSteps :
      Word.oddSteps (w.take k.1) = k.1 := by
    have hkLen : k.1 ≤ w.length := by
      simpa [Word.oddSteps] using Nat.le_of_lt k.isLt
    simp [Word.oddSteps, hkLen]
  have hGrowth :=
    h.logGrowth_lt_profile_add_one_add_correctionSum hFirst
  have hCorr :=
    h.logCorrectionSum_le_steps_div_three_mul_log_two
      hX hAbove
  rw [hSteps] at hCorr
  linarith

end Runs

namespace ActualFirstPassage

/--
actual critical first-passage run の任意の proper cut は actual prefix endpoint を持ち、
その endpoint で profile / phase / correction の exact decomposition が成り立つ。
-/
theorem exists_prefix_logGrowth_decomposition
    {w : Word}
    {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (k : Fin (Word.oddSteps w)) :
    ∃ z : ℕ, ∃ hPrefix : Runs (w.take k.1) x z,
      Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) =
        (Critical.profileFromWord w k : ℝ) +
          Experimental2.roofPhase
            (Experimental2.normalizeRoof Critical.beattyIndex)
            Bridge.collatzLogRotation k.1 +
          hPrefix.logCorrectionSum := by
  rcases h.run.exists_take_run k.1 with
    ⟨z, hPrefix, _hSuffix⟩
  exact ⟨z, hPrefix,
    hPrefix.logGrowth_eq_profile_add_roofPhase_add_correctionSum h.critical⟩

/--
full actual first-passage run が区間全体で `X>0` 以上なら、
任意の proper cut に actual endpoint があり、
その logarithmic growth は profile height から
幅 `1 + k/(3X ln2)` の corridor に入る。
-/
theorem exists_prefix_logGrowth_profile_corridor
    {X : ℕ}
    {w : Word}
    {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (hX : 0 < X)
    (hAbove : Runs.AllStartsAtLeast X w x)
    (k : Fin (Word.oddSteps w)) :
    ∃ z : ℕ, ∃ _hPrefix : Runs (w.take k.1) x z,
      (Critical.profileFromWord w k : ℝ) ≤
          Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) ∧
        Real.logb 2 (z : ℝ) - Real.logb 2 (x : ℝ) <
          (Critical.profileFromWord w k : ℝ) + 1 +
            (k.1 : ℝ) /
              (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  rcases h.run.exists_take_run k.1 with
    ⟨z, hPrefix, _hSuffix⟩
  have hPrefixAbove :
      Runs.AllStartsAtLeast X (w.take k.1) x :=
    hAbove.take k.1
  exact
    ⟨z, hPrefix,
      hPrefix.profile_le_logGrowth h.critical,
      hPrefix.logGrowth_lt_profile_add_one_add_uniformCorrection
        h.critical hX hPrefixAbove⟩

end ActualFirstPassage

end Collatz3
