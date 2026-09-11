import CollatzLean.Collatz3.Bridge.CollatzLogPhaseBounds
import CollatzLean.Collatz3.Semantics.Runs

import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: finite actual run の log₂ 位相 telescope

一歩の exact law

`phase(y) = fract(phase(x) + θ + δ(x))`

を finite `Runs` 全体へ telescope する。

この層では intermediate orbit を新しい packet field として保存しない。
また `Runs : Prop` の証明から `ℝ` を computational に取り出すこともしない。

finite run の correction 総和はまず endpoint residual

`log₂ y - log₂ x - n log₂ 3 + E`

として定義する。

actual `Runs` に対して、この residual が cons ごとに

`δ(x) + tail correction`

へ exact に分解することを derived theorem として証明する。
したがってこの residual は実際に run 上の `Σ δ(x_j)` そのものである。

さらに

* correction 総和の符号、
* finite run の exact phase telescope、
* 全 step start が `X` 以上の場合の一様上界

を導く。

この層では continued fraction / Ostrowski はまだ使わない。
-/

namespace Collatz3

namespace Bridge

/--
正の下限 `X` の下で一歩 correction に使う一様上界。

`1 / (3 X ln 2)`。
-/
noncomputable def collatzLogCorrectionCap (X : ℕ) : ℝ :=
  1 / (((3 : ℝ) * (X : ℝ)) * Real.log 2)

/--
`X ≤ x` なら correction(x) は `X` だけで決まる一様上界以下。
-/
theorem collatzLogCorrection_le_cap
    {X x : ℕ}
    (hX : 0 < X)
    (hXx : X ≤ x) :
    collatzLogCorrection x ≤ collatzLogCorrectionCap X := by
  have hx : 0 < x :=
    lt_of_lt_of_le hX hXx
  have hPoint :=
    collatzLogCorrection_le_inv_three_mul_log_two hx
  have hXR : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast hX
  have hXxR : (X : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hXx
  have hLog : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hDenX :
      (0 : ℝ) < ((3 : ℝ) * (X : ℝ)) * Real.log 2 := by
    positivity
  have hThree :
      (3 : ℝ) * (X : ℝ) ≤ (3 : ℝ) * (x : ℝ) := by
    nlinarith
  have hDenLe :
      ((3 : ℝ) * (X : ℝ)) * Real.log 2 ≤
        ((3 : ℝ) * (x : ℝ)) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hThree hLog.le
  have hInv :
      1 / (((3 : ℝ) * (x : ℝ)) * Real.log 2) ≤
        1 / (((3 : ℝ) * (X : ℝ)) * Real.log 2) :=
    one_div_le_one_div_of_le hDenX hDenLe
  exact le_trans hPoint hInv

/--
`fract(a+b)` では、`b` を先に fractional part へ落としても結果は同じ。

現在使用している mathlib revision には `Int.fract_add_fract` がないため、
`floor(b) + fract(b) = b` と integer-shift invariance から直接導く。
-/
theorem fract_add_eq_fract_add_fract
    (a b : ℝ) :
    Int.fract (a + b) =
      Int.fract (a + Int.fract b) := by
  calc
    Int.fract (a + b)
        =
      Int.fract
        (a + (((⌊b⌋ : ℤ) : ℝ) + Int.fract b)) := by
          rw [Int.floor_add_fract]
    _ =
      Int.fract
        ((a + Int.fract b) + ((⌊b⌋ : ℤ) : ℝ)) := by
          congr 1
          ring
    _ = Int.fract (a + Int.fract b) := by
          rw [Int.fract_add_intCast]

end Bridge

namespace Runs

/--
finite actual run に付随する correction residual。

`Runs` の証明自体から中間値を取り出すのではなく、

`log₂ y - log₂ x - n log₂ 3 + E`

という endpoint quantity として定義する。

actual run 上では `logCorrectionSum_cons` により

`δ(x₀) + δ(x₁) + ...`

へ exact に分解される。
-/
noncomputable def logCorrectionSum
    {w : Word}
    {x y : ℕ}
    (_h : Runs w x y) : ℝ :=
  Real.logb 2 (y : ℝ) -
    Real.logb 2 (x : ℝ) -
    (Word.oddSteps w : ℝ) * Real.logb 2 3 +
    (Word.twoSteps w : ℝ)

/--
空 run の correction residual は `0`。
-/
@[simp] theorem logCorrectionSum_nil
    (x : ℕ) :
    (Runs.nil x).logCorrectionSum = 0 := by
  unfold logCorrectionSum
  simp

/--
cons run の correction residual は

`head correction + tail correction`

へ exact に分解する。

これが endpoint residual が実際の `Σ δ(x_j)` であることの局所核。
-/
@[simp] theorem logCorrectionSum_cons
    {e : ℕ}
    {w : Word}
    {x m z : ℕ}
    (hstep : OddStep e x m)
    (htail : Runs w m z) :
    (Runs.cons hstep htail).logCorrectionSum =
      Bridge.collatzLogCorrection x +
        htail.logCorrectionSum := by
  unfold logCorrectionSum
  rw [
    hstep.logb_end_eq_start_add_logb_three_sub_exponent_add_correction
  ]
  simp only [
    Word.oddSteps_cons,
    Word.twoSteps_cons
  ]
  push_cast
  ring

/--
run の全 step start が `X` 以上であるという derived predicate。

`Runs : Prop` の証明自体を pattern match せず、
word の各 step より手前の actual prefix の終点を用いて特徴づける。

`w = u ++ e :: v` なら、prefix `u` の終点がその step の始点なので、
その値が常に `X` 以上であることを要求する。
-/
def AllStartsAtLeast
    (X : ℕ)
    {w : Word} {x y : ℕ}
    (_h : Runs w x y) : Prop :=
  ∀ {u v : Word} {e a : ℕ},
    w = u ++ e :: v →
    Runs u x a →
    X ≤ a

/-- 空 run には step start が存在しないので条件は自明。 -/
@[simp] theorem allStartsAtLeast_nil
    (X x : ℕ) :
    AllStartsAtLeast X (Runs.nil x) := by
  intro u v e a hw hu
  simp at hw

/-- nonempty run の最初の始点も当然 `X` 以上。 -/
theorem AllStartsAtLeast.head
    {X e : ℕ}
    {w : Word}
    {x m z : ℕ}
    {hstep : OddStep e x m}
    {htail : Runs w m z}
    (hAbove :
      AllStartsAtLeast X (Runs.cons hstep htail)) :
    X ≤ x := by
  apply hAbove
      (u := [])
      (v := w)
      (e := e)
      (a := x)
  · simp
  · exact Runs.nil x

/--
nonempty run 全体が `X` 以上なら、その tail の全 step start も `X` 以上。
-/
theorem AllStartsAtLeast.tail
    {X e : ℕ}
    {w : Word}
    {x m z : ℕ}
    {hstep : OddStep e x m}
    {htail : Runs w m z}
    (hAbove :
      AllStartsAtLeast X (Runs.cons hstep htail)) :
    AllStartsAtLeast X htail := by
  intro u v f a hw hu
  apply hAbove
      (u := e :: u)
      (v := v)
      (e := f)
      (a := a)
  · simp [hw]
  · exact Runs.cons hstep hu

/--
correction 総和は常に非負。
-/
theorem logCorrectionSum_nonneg
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    0 ≤ h.logCorrectionSum := by
  induction h with
  | nil x =>
      simp
  | @cons e w x m z hstep htail ih =>
      have hδ :
          0 < Bridge.collatzLogCorrection x :=
        hstep.logCorrection_pos
      rw [logCorrectionSum_cons hstep htail]
      exact add_nonneg hδ.le ih
/--
非空 run では correction 総和は strict に正。
-/
theorem logCorrectionSum_pos_of_nonempty
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ []) :
    0 < h.logCorrectionSum := by
  cases h with
  | nil x =>
      contradiction
  | @cons e w x m z hstep htail =>
      have hδ :
          0 < Bridge.collatzLogCorrection x :=
        hstep.logCorrection_pos
      have ht :
          0 ≤ htail.logCorrectionSum :=
        htail.logCorrectionSum_nonneg
      rw [logCorrectionSum_cons hstep htail]
      exact add_pos_of_pos_of_nonneg hδ ht

/--
finite run の raw `log₂` telescope。

`n = oddSteps w`, `E = twoSteps w` とすると

`log₂ y = log₂ x + n log₂3 - E + Σδ`。

correction sum を endpoint residual として定義しているので、
この identity 自体は定義から algebraically exact。
-/
theorem logb_end_eq_start_add_steps_sub_depth_add_correctionSum
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    Real.logb 2 (y : ℝ) =
      Real.logb 2 (x : ℝ) +
        (Word.oddSteps w : ℝ) * Real.logb 2 3 -
        (Word.twoSteps w : ℝ) +
        h.logCorrectionSum := by
  unfold logCorrectionSum
  ring

/--
前定理を canonical rotation

`θ = log₂(3/2) = log₂3 - 1`

と整数 shift に分離する。

整数 shift は

`oddSteps w - twoSteps w`

なので fractional part では消える。
-/
theorem logb_end_eq_run_rotation_add_integer
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    Real.logb 2 (y : ℝ) =
      (Real.logb 2 (x : ℝ) +
        (Word.oddSteps w : ℝ) * Bridge.collatzLogRotation +
        h.logCorrectionSum) +
      ((((Word.oddSteps w : ℤ) -
          (Word.twoSteps w : ℤ) : ℤ)) : ℝ) := by
  rw [
    h.logb_end_eq_start_add_steps_sub_depth_add_correctionSum
  ]
  rw [
    Bridge.collatzLogRotation_eq_logb_three_sub_one
  ]
  push_cast
  ring

/--
finite actual run の exact phase telescope。

`n` odd steps 後の位相は

`phase(y) = fract(phase(x) + n θ + Σδ)`。

個々の `v₂` / exponent は raw log の整数 shift に吸収され、
phase から完全に消える。
-/
theorem logPhase_run
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x +
          (Word.oddSteps w : ℝ) *
            Bridge.collatzLogRotation +
          h.logCorrectionSum) := by
  have hRaw :=
    h.logb_end_eq_run_rotation_add_integer
  unfold Bridge.collatzLogPhase
  rw [hRaw]
  rw [Int.fract_add_intCast]
  have hFract :=
    Bridge.fract_add_eq_fract_add_fract
      ((Word.oddSteps w : ℝ) *
        Bridge.collatzLogRotation +
        h.logCorrectionSum)
      (Real.logb 2 (x : ℝ))
  simpa [add_assoc, add_comm, add_left_comm] using hFract

/--
全 step start が `X > 0` 以上なら correction 総和は

`oddSteps(w) * (1 / (3 X ln 2))`

以下。
-/
theorem logCorrectionSum_le_steps_mul_cap
    {X : ℕ}
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X h) :
    h.logCorrectionSum ≤
      (Word.oddSteps w : ℝ) *
        Bridge.collatzLogCorrectionCap X := by
  induction h with
  | nil x =>
      simp
  | @cons e w x m z hstep htail ih =>
      have hx : X ≤ x :=
        AllStartsAtLeast.head
          (hstep := hstep)
          (htail := htail)
          hAbove
      have htailAbove : AllStartsAtLeast X htail :=
        AllStartsAtLeast.tail
          (hstep := hstep)
          (htail := htail)
          hAbove
      have hδ :
          Bridge.collatzLogCorrection x ≤
            Bridge.collatzLogCorrectionCap X :=
        Bridge.collatzLogCorrection_le_cap hX hx
      have ht :=
        ih htailAbove
      rw [logCorrectionSum_cons hstep htail]
      simp only [Word.oddSteps_cons]
      push_cast
      calc
        Bridge.collatzLogCorrection x +
              htail.logCorrectionSum
            ≤ Bridge.collatzLogCorrectionCap X +
                (Word.oddSteps w : ℝ) *
                  Bridge.collatzLogCorrectionCap X :=
          add_le_add hδ ht
        _ = ((Word.oddSteps w : ℝ) + 1) *
              Bridge.collatzLogCorrectionCap X := by
          ring

/--
上の評価を

`n / (3 X ln 2)`

の表示へ直した版。
-/
theorem logCorrectionSum_le_steps_div_three_mul_log_two
    {X : ℕ}
    {w : Word}
    {x y : ℕ}
    (h : Runs w x y)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X h) :
    h.logCorrectionSum ≤
      (Word.oddSteps w : ℝ) /
        (((3 : ℝ) * (X : ℝ)) * Real.log 2) := by
  simpa [
    Bridge.collatzLogCorrectionCap,
    div_eq_mul_inv
  ] using
    h.logCorrectionSum_le_steps_mul_cap hX hAbove

end Runs

end Collatz3
