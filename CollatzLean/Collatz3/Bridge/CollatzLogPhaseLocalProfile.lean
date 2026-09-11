import CollatzLean.Collatz3.Bridge.CollatzLogPhaseProfile

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual local interval の log₂ growth と critical profile 差

`CollatzLogPhaseProfile` では、始点 `x` から proper cut `k` までの actual growth を

`profile(k) + normalized Beatty phase(k) + correctionSum(k)`

へ exact に分解した。

このファイルでは二つの proper cut `a,b` を比較し、その差を取る。
新しい segment structure は導入せず、

* `w.take a` の actual prefix、
* そこから `w.take b` までの actual local run、

だけを用いる。

結果として local interval `[a,b]` では

`log₂ x_b - log₂ x_a`

が exact に

* full profile の差、
* normalized Beatty mechanical phase の差、
* local Collatz correction sum

へ分解される。

さらに phase 差が `(-1,1)` に入り、local correction が非負であることから、
高い軌道区間では

`profile(b)-profile(a)-1`

と

`profile(b)-profile(a)+1+(b-a)/(3X ln 2)`

の間に local logarithmic growth が入る。

RecordFerrers / canonical partition / Ostrowski decomposition はまだ使わない。
-/

namespace Collatz3

namespace Runs

/--
finite actual run を append したとき、endpoint residual として定義した
`logCorrectionSum` も exact に加法的。

proof object から中間値を抽出せず、endpoint residual の定義だけから導く。
-/
@[simp] theorem logCorrectionSum_append
    {u v : Word}
    {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v y z) :
    (hu.append hv).logCorrectionSum =
      hu.logCorrectionSum + hv.logCorrectionSum := by
  unfold logCorrectionSum
  simp only [Word.oddSteps_append, Word.twoSteps_append]
  push_cast
  ring

/--
同じ full run 上で `a ≤ b` なら、`take a` endpoint から `take b` endpoint までの
actual local run を取り出せる。

local word は新しい primitive にせず、存在量としてだけ返す。
-/
theorem exists_between_take
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    {a b : ℕ}
    (hab : a ≤ b) :
    ∃ xa xb : ℕ, ∃ u : Word,
      Runs (w.take a) x xa ∧
        Runs u xa xb ∧
        Runs (w.take b) x xb ∧
        w.take b = w.take a ++ u := by
  rcases h.exists_take_run b with
    ⟨xb, hB, _hAfterB⟩
  rcases hB.exists_take_run a with
    ⟨xa, hARaw, hLocalRaw⟩
  have hTake :
      (w.take b).take a = w.take a := by
    simp [List.take_take, Nat.min_eq_left hab]
  have hA : Runs (w.take a) x xa := by
    simpa [hTake] using hARaw
  let u : Word := (w.take b).drop a
  have hLocal : Runs u xa xb := by
    simpa [u] using hLocalRaw
  have hWord :
      w.take b = w.take a ++ u := by
    dsimp [u]
    calc
      w.take b = (w.take b).take a ++ (w.take b).drop a := by
        symm
        exact List.take_append_drop a (w.take b)
      _ = w.take a ++ (w.take b).drop a := by
        rw [hTake]
  exact ⟨xa, xb, u, hA, hLocal, hB, hWord⟩

/--
`take b = take a ++ u` かつ両 cut が word 内なら、local word の odd-step 数は exact に `b-a`。
-/
theorem oddSteps_eq_sub_of_take_append
    {w u : Word}
    {a b : ℕ}
    (ha : a ≤ Word.oddSteps w)
    (hb : b ≤ Word.oddSteps w)
    (hWord : w.take b = w.take a ++ u) :
    Word.oddSteps u = b - a := by
  have haLen : a ≤ w.length := by
    simpa [Word.oddSteps] using ha
  have hbLen : b ≤ w.length := by
    simpa [Word.oddSteps] using hb
  have hTakeA : Word.oddSteps (w.take a) = a := by
    simp [Word.oddSteps, haLen]
  have hTakeB : Word.oddSteps (w.take b) = b := by
    simp [Word.oddSteps, hbLen]
  have hEq := congrArg Word.oddSteps hWord
  rw [hTakeB, Word.oddSteps_append, hTakeA] at hEq
  omega

/--
full run の全 step start が `X` 以上なら、
`take a` の endpoint から始まる local subrun も同じ下限を保つ。

`take b = take a ++ u` を full word の prefix decomposition へ埋め込むだけである。
-/
theorem allStartsAtLeast_local_of_take_append
    {X : ℕ}
    {w u : Word}
    {x xa : ℕ}
    (hAbove : AllStartsAtLeast X w x)
    {a b : ℕ}
    (hA : Runs (w.take a) x xa)
    (hWord : w.take b = w.take a ++ u) :
    AllStartsAtLeast X u xa := by
  intro p q e c hU hp
  apply hAbove
      (u := w.take a ++ p)
      (v := q ++ w.drop b)
      (e := e)
      (a := c)
  · calc
      w = w.take b ++ w.drop b := by
        symm
        exact List.take_append_drop b w
      _ = (w.take a ++ u) ++ w.drop b := by
        rw [hWord]
      _ = (w.take a ++ (p ++ e :: q)) ++ w.drop b := by
        rw [hU]
      _ = (w.take a ++ p) ++ e :: (q ++ w.drop b) := by
        simp [List.append_assoc]
  · exact hA.append hp

end Runs

namespace Bridge

/--
二つの normalized Beatty phase の差は strict に `-1` より大きい。
-/
theorem normalizedBeattyLogPhase_sub_gt_neg_one
    (a b : ℕ) :
    -1 <
      Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          collatzLogRotation b -
        Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          collatzLogRotation a := by
  have hB := normalizedBeattyLogPhase_nonneg b
  have hA := normalizedBeattyLogPhase_lt_one a
  linarith

/--
二つの normalized Beatty phase の差は strict に `1` 未満。
-/
theorem normalizedBeattyLogPhase_sub_lt_one
    (a b : ℕ) :
    Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          collatzLogRotation b -
        Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          collatzLogRotation a < 1 := by
  have hB := normalizedBeattyLogPhase_lt_one b
  have hA := normalizedBeattyLogPhase_nonneg a
  linarith

end Bridge

namespace Runs

/--
二つの proper cut `a,b` の間の actual logarithmic growth の exact local decomposition。

`take b = take a ++ u` によって local run `u` が二つの prefix を exact に連結しているとする。
二本の global-prefix identity を引き算し、`logCorrectionSum_append` で local correction だけを残す。
-/
theorem logGrowth_local_eq_profileDiff_add_roofPhaseDiff_add_correctionSum
    {w : Word}
    {a b : Fin (Word.oddSteps w)}
    {x xa xb : ℕ}
    {u : Word}
    (hA : Runs (w.take a.1) x xa)
    (hLocal : Runs u xa xb)
    (hWord : w.take b.1 = w.take a.1 ++ u)
    (hFirst : Word.CriticalFirstPassage w) :
    Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) =
      ((Critical.profileFromWord w b : ℝ) -
        (Critical.profileFromWord w a : ℝ)) +
      (Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          Bridge.collatzLogRotation b.1 -
        Experimental2.roofPhase
          (Experimental2.normalizeRoof Critical.beattyIndex)
          Bridge.collatzLogRotation a.1) +
      hLocal.logCorrectionSum := by
  have hB : Runs (w.take b.1) x xb := by
    rw [hWord]
    exact hA.append hLocal
  have hAEq :=
    hA.logGrowth_eq_profile_add_roofPhase_add_correctionSum hFirst
  have hBEq :=
    hB.logGrowth_eq_profile_add_roofPhase_add_correctionSum hFirst
  have hCorr :
      hB.logCorrectionSum =
        hA.logCorrectionSum + hLocal.logCorrectionSum := by
    unfold logCorrectionSum
    rw [hWord]
    simp only [Word.oddSteps_append, Word.twoSteps_append]
    push_cast
    ring
  linarith

/--
local growth は profile 差より `1` 以上下へは行けない。

normalized mechanical phase 差が `>-1`、local correction が非負であることだけを使う。
-/
theorem profileDiff_sub_one_lt_logGrowth_local
    {w : Word}
    {a b : Fin (Word.oddSteps w)}
    {x xa xb : ℕ}
    {u : Word}
    (hA : Runs (w.take a.1) x xa)
    (hLocal : Runs u xa xb)
    (hWord : w.take b.1 = w.take a.1 ++ u)
    (hFirst : Word.CriticalFirstPassage w) :
    ((Critical.profileFromWord w b : ℝ) -
        (Critical.profileFromWord w a : ℝ)) - 1 <
      Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) := by
  have hEq :=
    hA.logGrowth_local_eq_profileDiff_add_roofPhaseDiff_add_correctionSum
      hLocal hWord hFirst
  have hPhase :=
    Bridge.normalizedBeattyLogPhase_sub_gt_neg_one a.1 b.1
  have hCorr := hLocal.logCorrectionSum_nonneg
  linarith

/--
local growth は

`profile difference + 1 + local correction sum`

より strict に小さい。
-/
theorem logGrowth_local_lt_profileDiff_add_one_add_correctionSum
    {w : Word}
    {a b : Fin (Word.oddSteps w)}
    {x xa xb : ℕ}
    {u : Word}
    (hA : Runs (w.take a.1) x xa)
    (hLocal : Runs u xa xb)
    (hWord : w.take b.1 = w.take a.1 ++ u)
    (hFirst : Word.CriticalFirstPassage w) :
    Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) <
      ((Critical.profileFromWord w b : ℝ) -
        (Critical.profileFromWord w a : ℝ)) + 1 +
      hLocal.logCorrectionSum := by
  have hEq :=
    hA.logGrowth_local_eq_profileDiff_add_roofPhaseDiff_add_correctionSum
      hLocal hWord hFirst
  have hPhase :=
    Bridge.normalizedBeattyLogPhase_sub_lt_one a.1 b.1
  linarith

/--
local run 全体が `X>0` 以上なら correction を一様評価して、
local growth を local word length だけで上から抑えられる。
-/
theorem logGrowth_local_lt_profileDiff_add_one_add_uniformCorrection
    {X : ℕ}
    {w : Word}
    {a b : Fin (Word.oddSteps w)}
    {x xa xb : ℕ}
    {u : Word}
    (hA : Runs (w.take a.1) x xa)
    (hLocal : Runs u xa xb)
    (hWord : w.take b.1 = w.take a.1 ++ u)
    (hFirst : Word.CriticalFirstPassage w)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X u xa) :
    Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) <
      ((Critical.profileFromWord w b : ℝ) -
        (Critical.profileFromWord w a : ℝ)) + 1 +
      (Word.oddSteps u : ℝ) /
        (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  have hGrowth :=
    hA.logGrowth_local_lt_profileDiff_add_one_add_correctionSum
      hLocal hWord hFirst
  have hCorr :=
    hLocal.logCorrectionSum_le_steps_div_three_mul_log_two
      hX hAbove
  linarith

/--
proper cuts `a,b` を結ぶ local word では `oddSteps u = b-a` なので、
高い local interval 上の上界を cut distance だけで書ける。
-/
theorem logGrowth_local_lt_profileDiff_add_one_add_cutDistanceCorrection
    {X : ℕ}
    {w : Word}
    {a b : Fin (Word.oddSteps w)}
    {x xa xb : ℕ}
    {u : Word}
    (hA : Runs (w.take a.1) x xa)
    (hLocal : Runs u xa xb)
    (hWord : w.take b.1 = w.take a.1 ++ u)
    (hFirst : Word.CriticalFirstPassage w)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X u xa) :
    Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) <
      ((Critical.profileFromWord w b : ℝ) -
        (Critical.profileFromWord w a : ℝ)) + 1 +
      ((b.1 - a.1 : ℕ) : ℝ) /
        (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  have haLe : a.1 ≤ Word.oddSteps w :=
    Nat.le_of_lt a.2
  have hbLe : b.1 ≤ Word.oddSteps w :=
    Nat.le_of_lt b.2
  have hSteps :
      Word.oddSteps u = b.1 - a.1 :=
    oddSteps_eq_sub_of_take_append haLe hbLe hWord
  have hGrowth :=
    hA.logGrowth_local_lt_profileDiff_add_one_add_uniformCorrection
      hLocal hWord hFirst hX hAbove
  rw [hSteps] at hGrowth
  exact hGrowth

end Runs

namespace ActualFirstPassage

/--
任意の ordered proper cuts `a≤b` に対し、actual local interval と exact profile/phase/correction
分解を同時に取り出す。
-/
theorem exists_local_logGrowth_decomposition
    {w : Word}
    {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (a b : Fin (Word.oddSteps w))
    (hab : a.1 ≤ b.1) :
    ∃ xa xb : ℕ, ∃ u : Word,
      ∃ _hA : Runs (w.take a.1) x xa,
      ∃ hLocal : Runs u xa xb,
        w.take b.1 = w.take a.1 ++ u ∧
        Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) =
          ((Critical.profileFromWord w b : ℝ) -
            (Critical.profileFromWord w a : ℝ)) +
          (Experimental2.roofPhase
              (Experimental2.normalizeRoof Critical.beattyIndex)
              Bridge.collatzLogRotation b.1 -
            Experimental2.roofPhase
              (Experimental2.normalizeRoof Critical.beattyIndex)
              Bridge.collatzLogRotation a.1) +
          hLocal.logCorrectionSum := by
  rcases h.run.exists_between_take hab with
    ⟨xa, xb, u, hA, hLocal, _hB, hWord⟩
  refine ⟨xa, xb, u, hA, hLocal, hWord, ?_⟩
  exact
    hA.logGrowth_local_eq_profileDiff_add_roofPhaseDiff_add_correctionSum
      hLocal hWord h.critical

/--
full actual first-passage run の全 step start が `X>0` 以上なら、
任意の ordered proper interval `[a,b]` の local logarithmic growth は

`profile(b)-profile(a)-1`

と

`profile(b)-profile(a)+1+(b-a)/(3X ln2)`

の間に入る。
-/
theorem exists_local_logGrowth_profile_corridor
    {X : ℕ}
    {w : Word}
    {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (hX : 0 < X)
    (hAbove : Runs.AllStartsAtLeast X w x)
    (a b : Fin (Word.oddSteps w))
    (hab : a.1 ≤ b.1) :
    ∃ xa xb : ℕ, ∃ u : Word,
      ∃ _hA : Runs (w.take a.1) x xa,
      ∃ _hLocal : Runs u xa xb,
        w.take b.1 = w.take a.1 ++ u ∧
        ((Critical.profileFromWord w b : ℝ) -
            (Critical.profileFromWord w a : ℝ)) - 1 <
          Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) ∧
        Real.logb 2 (xb : ℝ) - Real.logb 2 (xa : ℝ) <
          ((Critical.profileFromWord w b : ℝ) -
            (Critical.profileFromWord w a : ℝ)) + 1 +
          ((b.1 - a.1 : ℕ) : ℝ) /
            (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  rcases h.run.exists_between_take hab with
    ⟨xa, xb, u, hA, hLocal, _hB, hWord⟩
  have hLocalAbove : Runs.AllStartsAtLeast X u xa :=
    Runs.allStartsAtLeast_local_of_take_append
      hAbove hA hWord
  refine ⟨xa, xb, u, hA, hLocal, hWord, ?_, ?_⟩
  · exact
      hA.profileDiff_sub_one_lt_logGrowth_local
        hLocal hWord h.critical
  · exact
      hA.logGrowth_local_lt_profileDiff_add_one_add_cutDistanceCorrection
        hLocal hWord h.critical hX hLocalAbove

end ActualFirstPassage

end Collatz3
