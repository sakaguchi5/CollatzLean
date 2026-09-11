import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog
import CollatzLean.Collatz3.Experimental2.RotationPhase

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: actual log₂ phase と pure mechanical phase

actual odd-only Collatz の log₂ phase と、正規化 Beatty roof が与える
pure mechanical phase を exact に比較する。

このファイルで追加する公開定理は三本だけである。

1. normalized Beatty mechanical phase は `fract(n * θ)` そのもの。
2. actual phase は「初期 actual phase + mechanical phase + correction sum」。
3. 非空 actual run の終点 phase は、時刻 `n` の pure mechanical phase そのものとは一致しない。

ここで `θ = log₂(3/2)`、correction は Collatz の `+1` に由来する。
新しい primitive data は導入しない。
-/

namespace Collatz3
namespace Bridge

/--
正規化 Beatty roof の mechanical phase は pure rotation の fractional part そのもの。

`normalizeRoof beattyIndex n = floor(n * log₂(3/2))` と
`floor + fract = identity` を直接つなぐ。
-/
theorem normalizedBeattyLogPhase_eq_fract_rotation
    (n : ℕ) :
    Experimental2.roofPhase
        (Experimental2.normalizeRoof Critical.beattyIndex)
        collatzLogRotation n =
      Int.fract ((n : ℝ) * collatzLogRotation) := by
  have hFloor :
      Experimental2.normalizeRoof Critical.beattyIndex n =
        ⌊(n : ℝ) * collatzLogRotation⌋₊ := by
    simpa [collatzLogRotation] using
      normalizeBeatty_eq_natFloor_logb_three_halves n
  have hRotationNonneg : 0 ≤ collatzLogRotation := by
    unfold collatzLogRotation
    exact Real.logb_nonneg (by norm_num) (by norm_num)
  have hNonneg :
      0 ≤ (n : ℝ) * collatzLogRotation :=
    mul_nonneg (Nat.cast_nonneg n) hRotationNonneg
  have hFloorInt :
      (⌊(n : ℝ) * collatzLogRotation⌋₊ : ℤ) =
        ⌊(n : ℝ) * collatzLogRotation⌋ :=
    Int.natCast_floor_eq_floor hNonneg
  have hFloorCast :
      ((⌊(n : ℝ) * collatzLogRotation⌋₊ : ℕ) : ℝ) =
        ((⌊(n : ℝ) * collatzLogRotation⌋ : ℤ) : ℝ) := by
    exact_mod_cast hFloorInt
  unfold Experimental2.roofPhase
  rw [hFloor, hFloorCast]
  have hDecomp :=
    Int.floor_add_fract ((n : ℝ) * collatzLogRotation)
  linarith

/--
actual finite run の終点 phase は、初期 actual phase に
normalized Beatty mechanical phase と Collatz correction sum を足したもの。

したがって actual dynamics と pure mechanical dynamics の差は、
exact に initial phase と `+1` correction に分離される。
-/
theorem actualLogPhase_eq_correctedMechanicalPhase
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    collatzLogPhase y =
      Int.fract
        (collatzLogPhase x +
          Experimental2.roofPhase
            (Experimental2.normalizeRoof Critical.beattyIndex)
            collatzLogRotation (Word.oddSteps w) +
          h.logCorrectionSum) := by
  rw [h.logPhase_run]
  have hFract :=
    fract_add_eq_fract_add_fract
      (collatzLogPhase x + h.logCorrectionSum)
      ((Word.oddSteps w : ℝ) * collatzLogRotation)
  simpa [
    normalizedBeattyLogPhase_eq_fract_rotation,
    add_assoc, add_comm, add_left_comm
  ] using hFract

/-- fractional part が等しければ、元の二実数の差は整数。 -/
private theorem sub_eq_intCast_of_fract_eq
    {a b : ℝ}
    (h : Int.fract a = Int.fract b) :
    ∃ z : ℤ, a - b = (z : ℝ) := by
  refine ⟨⌊a⌋ - ⌊b⌋, ?_⟩
  have ha := Int.floor_add_fract a
  have hb := Int.floor_add_fract b
  rw [h] at ha
  push_cast
  linarith

/-- actual odd-only 一歩の終点は `3` で割れない。 -/
private theorem oddStep_end_not_dvd_three
    {e x y : ℕ}
    (h : OddStep e x y) :
    ¬ 3 ∣ y := by
  intro hThree
  rcases hThree with ⟨q, hq⟩
  have hEq := h.equation
  rw [hq] at hEq
  have hEq' :
      3 * (2 ^ e * q) = 3 * x + 1 := by
    calc
      3 * (2 ^ e * q) = 2 ^ e * (3 * q) := by ring
      _ = 3 * x + 1 := hEq
  omega

/-- 非空 actual run の最後の odd endpoint も `3` で割れない。 -/
private theorem runs_end_not_dvd_three_of_nonempty
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    w ≠ [] → ¬ 3 ∣ y := by
  induction h with
  | nil x =>
      intro hne
      exact False.elim (hne rfl)
  | @cons e w x m z hstep htail ih =>
      intro _hne
      by_cases hw : w = []
      · subst w
        cases htail
        exact oddStep_end_not_dvd_three hstep
      · exact ih hw

/--
非空 actual run の終点 log₂ phase は、同じ odd-step 数だけ進めた
pure normalized Beatty mechanical phase そのものとは一致しない。

仮に一致すると二つの fractional part が等しいので、

`log₂ y - n log₂ 3`

は整数になる。base `2` で指数化すると、整数の符号に応じて

* `y = 3^n * 2^q`、または
* `y * 2^(q+1) = 3^n`

を得る。どちらの場合も `n>0` なら `3 ∣ y` が従う。
しかし actual odd-only step の終点は常に `3` で割れないため矛盾する。
-/
theorem actualLogPhase_ne_pureMechanicalPhase_of_nonempty
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    collatzLogPhase y ≠
      Experimental2.roofPhase
        (Experimental2.normalizeRoof Critical.beattyIndex)
        collatzLogRotation (Word.oddSteps w) := by
  intro hEq
  let n : ℕ := Word.oddSteps w
  have hnPos : 0 < n := by
    dsimp [n, Word.oddSteps]
    exact List.length_pos_iff.mpr hne
  have hyOdd : Odd y :=
    h.end_odd_of_nonempty hne
  have hyPos : 0 < y := by
    rcases hyOdd with ⟨k, hk⟩
    omega
  have hyRPos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast hyPos
  have hPhase :
      Int.fract (Real.logb 2 (y : ℝ)) =
        Int.fract ((n : ℝ) * collatzLogRotation) := by
    unfold collatzLogPhase at hEq
    rw [normalizedBeattyLogPhase_eq_fract_rotation] at hEq
    simpa [n] using hEq
  obtain ⟨z, hz⟩ :=
    sub_eq_intCast_of_fract_eq hPhase
  let j : ℤ := z - (n : ℤ)
  have hLog :
      Real.logb 2 (y : ℝ) =
        (n : ℝ) * Real.logb 2 3 + (j : ℝ) := by
    rw [collatzLogRotation_eq_logb_three_sub_one] at hz
    dsimp [j]
    push_cast at hz ⊢
    linarith
  have hExp :
      (2 : ℝ) ^
          ((n : ℝ) * Real.logb 2 3 + (j : ℝ)) =
        (y : ℝ) :=
    (Real.logb_eq_iff_rpow_eq
      (b := (2 : ℝ))
      (x := (n : ℝ) * Real.logb 2 3 + (j : ℝ))
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
      hyRPos).1 hLog
  have hThreeRpow :
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 3) =
        (3 : ℝ) ^ n := by
    rw [← Real.logb_pow]
    exact
      Real.rpow_logb
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)
        (by positivity : (0 : ℝ) < (3 : ℝ) ^ n)
  have hFactor :
      (y : ℝ) =
        (3 : ℝ) ^ n * (2 : ℝ) ^ (j : ℝ) := by
    calc
      (y : ℝ) =
          (2 : ℝ) ^
            ((n : ℝ) * Real.logb 2 3 + (j : ℝ)) :=
        hExp.symm
      _ =
          (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 3) *
            (2 : ℝ) ^ (j : ℝ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (3 : ℝ) ^ n * (2 : ℝ) ^ (j : ℝ) := by
        rw [hThreeRpow]
  rw [Real.rpow_intCast] at hFactor
  have hNoThree : ¬ 3 ∣ y :=
    runs_end_not_dvd_three_of_nonempty h hne
  cases hj : j with
  | ofNat q =>
      rw [hj] at hFactor
      change
        (y : ℝ) =
          (3 : ℝ) ^ n * (2 : ℝ) ^ q
        at hFactor
      have hFactorNat :
          y = 3 ^ n * 2 ^ q := by
        exact_mod_cast hFactor
      have hThreePow : 3 ∣ 3 ^ n :=
        dvd_pow_self 3 (Nat.ne_of_gt hnPos)
      have hThreeY : 3 ∣ y := by
        rw [hFactorNat]
        exact dvd_mul_of_dvd_left hThreePow (2 ^ q)
      exact hNoThree hThreeY
  | negSucc q =>
      rw [hj] at hFactor
      rw [zpow_negSucc] at hFactor
      have hTwoPowNe :
          (2 : ℝ) ^ (q + 1) ≠ 0 := by
        positivity
      have hCross :
          (y : ℝ) * (2 : ℝ) ^ (q + 1) =
            (3 : ℝ) ^ n := by
        calc
          (y : ℝ) * (2 : ℝ) ^ (q + 1) =
              ((3 : ℝ) ^ n * ((2 : ℝ) ^ (q + 1))⁻¹) *
                (2 : ℝ) ^ (q + 1) := by
            rw [hFactor]
          _ = (3 : ℝ) ^ n := by
            field_simp [hTwoPowNe]
      have hCrossNat :
          y * 2 ^ (q + 1) = 3 ^ n := by
        exact_mod_cast hCross
      have hThreePow : 3 ∣ 3 ^ n :=
        dvd_pow_self 3 (Nat.ne_of_gt hnPos)
      have hThreeProd : 3 ∣ y * 2 ^ (q + 1) := by
        rw [hCrossNat]
        exact hThreePow
      rcases Nat.prime_three.dvd_mul.mp hThreeProd with
        hThreeY | hThreeTwoPow
      · exact hNoThree hThreeY
      · have hThreeTwo : 3 ∣ 2 :=
          Nat.prime_three.dvd_of_dvd_pow hThreeTwoPow
        norm_num at hThreeTwo

end Bridge
end Collatz3
