import CollatzLean.Collatz3.Bridge.CollatzLogPhaseLocalProfile
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseNearReturn

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: canonical Ostrowski block の log-phase stability

単一 convergent weight `q_n` に対する near-return を、任意の block length `r` へ拡張する。

`r` の horizontal canonical Ostrowski digits を `d_i` とすると

`r = Σ d_i q_i`

であり、各 basic weight は

`q_i * log₂(3/2) = integer_i + error_i`

を満たす。従って block 全体でも

`r * log₂(3/2) = integer(r) + Σ d_i error_i`

という exact decomposition が得られる。

このファイルでは

* arbitrary digit prefix の composite integer / error / error cap、
* canonical block length `r` への specialization、
* actual `Runs` の phase shift への exact 接続、
* high orbit 上の total shift bound、
* pure Ostrowski argument に Collatz correction を加えたときの threshold-side stability

までを扱う。

actual Collatz 側に新しい carry を定義しない。
RecordFerrers / record carry との接続は次の Bridge 層へ残す。
-/

namespace Collatz3
open Experimental2
namespace Bridge

namespace BeattyRegularOstrowskiSystem

/--
任意 digit 列 `d` の先頭 `t` 桁について、basic near-return の整数部分を足し上げる。

horizontal weight `i` は `P_(i+1)` なので、対応する整数部分は
`Q_(i+1)-P_(i+1)`。
-/
def horizontalOstrowskiRotationIntegerPrefix
    (D : BeattyRegularOstrowskiSystem)
    (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      horizontalOstrowskiRotationIntegerPrefix D d n +
        (d n : ℤ) *
          ((D.conv.Q (n + 1) : ℤ) - (D.conv.P (n + 1) : ℤ))

/--
任意 digit 列 `d` の先頭 `t` 桁について、basic rotation return error を足し上げる。
-/
noncomputable def horizontalOstrowskiRotationErrorPrefix
    (D : BeattyRegularOstrowskiSystem)
    (d : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      horizontalOstrowskiRotationErrorPrefix D d n +
        (d n : ℝ) * D.horizontalRotationReturnError n

/--
triangle inequality だけで使う composite error の安全な上界。

各 basic error に既証明の `1 / q_(i+1)` 上界を入れたもの。
-/
noncomputable def horizontalOstrowskiRotationErrorCapPrefix
    (D : BeattyRegularOstrowskiSystem)
    (d : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      horizontalOstrowskiRotationErrorCapPrefix D d n +
        (d n : ℝ) /
          ((D.horizontalWeights).Q (n + 1) : ℝ)

/--
任意 finite digit prefix の exact rotation decomposition。

`S_t = Σ_{i<t} d_i q_i` とすると

`S_t * θ = integerPrefix + errorPrefix`。

Ostrowski canonicality は不要で、weighted sum の再帰だけを使う。
-/
theorem horizontalOstrowskiRotationPrefix_decomposition
    (D : BeattyRegularOstrowskiSystem)
    (d : ℕ → ℕ) :
    ∀ t : ℕ,
      (ostrowskiPrefixSum (D.horizontalWeights).Q d t : ℝ) *
          collatzLogRotation =
        ((D.horizontalOstrowskiRotationIntegerPrefix d t : ℤ) : ℝ) +
          D.horizontalOstrowskiRotationErrorPrefix d t := by
  intro t
  induction t with
  | zero =>
      simp [horizontalOstrowskiRotationIntegerPrefix,
        horizontalOstrowskiRotationErrorPrefix]
  | succ n ih =>
      have hAtom :
          ((D.horizontalWeights).Q n : ℝ) * collatzLogRotation =
            (((D.conv.Q (n + 1) : ℤ) -
                (D.conv.P (n + 1) : ℤ) : ℤ) : ℝ) +
              D.horizontalRotationReturnError n := by
        unfold horizontalRotationReturnError
        ring
      rw [ostrowskiPrefixSum_succ]
      rw [horizontalOstrowskiRotationIntegerPrefix,
        horizontalOstrowskiRotationErrorPrefix]
      push_cast
      rw [add_mul]
      rw [ih]
      calc
        _ =
            (↑(D.horizontalOstrowskiRotationIntegerPrefix d n) +
              D.horizontalOstrowskiRotationErrorPrefix d n) +
            (d n : ℝ) *
              (((D.horizontalWeights).Q n : ℝ) *
                collatzLogRotation) := by
          ring
        _ = _ := by
          rw [hAtom]
          push_cast
          ring

/--
任意 digit prefix の composite rotation error は basic error bound の digit-weighted sum 以下。
-/
theorem abs_horizontalOstrowskiRotationErrorPrefix_le_cap
    (D : BeattyRegularOstrowskiSystem)
    (d : ℕ → ℕ) :
    ∀ t : ℕ,
      |D.horizontalOstrowskiRotationErrorPrefix d t| ≤
        D.horizontalOstrowskiRotationErrorCapPrefix d t := by
  intro t
  induction t with
  | zero =>
      simp [horizontalOstrowskiRotationErrorPrefix,
        horizontalOstrowskiRotationErrorCapPrefix]
  | succ n ih =>
      have hErr :
          |D.horizontalRotationReturnError n| ≤
            1 / ((D.horizontalWeights).Q (n + 1) : ℝ) :=
        le_of_lt (D.abs_horizontalRotationReturnError_lt_inv_nextWeight n)
      have hd : (0 : ℝ) ≤ (d n : ℝ) := by positivity
      have hTerm :
          |(d n : ℝ) * D.horizontalRotationReturnError n| ≤
            (d n : ℝ) /
              ((D.horizontalWeights).Q (n + 1) : ℝ) := by
        rw [abs_mul, abs_of_nonneg hd]
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hErr hd
      rw [horizontalOstrowskiRotationErrorPrefix,
        horizontalOstrowskiRotationErrorCapPrefix]
      calc
        |D.horizontalOstrowskiRotationErrorPrefix d n +
            (d n : ℝ) * D.horizontalRotationReturnError n|
            ≤ |D.horizontalOstrowskiRotationErrorPrefix d n| +
                |(d n : ℝ) * D.horizontalRotationReturnError n| :=
          abs_add_le _ _
        _ ≤ D.horizontalOstrowskiRotationErrorCapPrefix d n +
              (d n : ℝ) /
                ((D.horizontalWeights).Q (n + 1) : ℝ) :=
          add_le_add ih hTerm

/-- canonical horizontal digits で作る block の整数部分。 -/
def horizontalOstrowskiBlockInteger
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) : ℤ :=
  D.horizontalOstrowskiRotationIntegerPrefix
    (D.horizontalOstrowskiDigits r) (r + 1)

/-- canonical horizontal digits で作る block の composite rotation error。 -/
noncomputable def horizontalOstrowskiBlockError
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) : ℝ :=
  D.horizontalOstrowskiRotationErrorPrefix
    (D.horizontalOstrowskiDigits r) (r + 1)

/-- canonical horizontal digits で作る composite rotation error の安全な上界。 -/
noncomputable def horizontalOstrowskiBlockErrorCap
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) : ℝ :=
  D.horizontalOstrowskiRotationErrorCapPrefix
    (D.horizontalOstrowskiDigits r) (r + 1)

/--
任意 block length `r` の canonical horizontal Ostrowski decomposition による exact rotation law。
-/
theorem horizontalOstrowskiBlock_decomposition
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) :
    (r : ℝ) * collatzLogRotation =
      ((D.horizontalOstrowskiBlockInteger r : ℤ) : ℝ) +
        D.horizontalOstrowskiBlockError r := by
  have h :=
    D.horizontalOstrowskiRotationPrefix_decomposition
      (D.horizontalOstrowskiDigits r) (r + 1)
  rw [D.horizontalOstrowskiDigits_reconstruct r] at h
  simpa [horizontalOstrowskiBlockInteger,
    horizontalOstrowskiBlockError] using h

/--
canonical block の pure rotation fractional part は composite error だけで決まる。
-/
theorem fract_mul_rotation_eq_fract_blockError
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) :
    Int.fract ((r : ℝ) * collatzLogRotation) =
      Int.fract (D.horizontalOstrowskiBlockError r) := by
  rw [D.horizontalOstrowskiBlock_decomposition r]
  calc
    Int.fract
        (((D.horizontalOstrowskiBlockInteger r : ℤ) : ℝ) +
          D.horizontalOstrowskiBlockError r) =
      Int.fract
        (D.horizontalOstrowskiBlockError r +
          ((D.horizontalOstrowskiBlockInteger r : ℤ) : ℝ)) := by
        rw [add_comm]
    _ = Int.fract (D.horizontalOstrowskiBlockError r) := by
      rw [Int.fract_add_intCast]

/-- canonical block composite error の absolute bound。 -/
theorem abs_horizontalOstrowskiBlockError_le_cap
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) :
    |D.horizontalOstrowskiBlockError r| ≤
      D.horizontalOstrowskiBlockErrorCap r := by
  simpa [horizontalOstrowskiBlockError,
    horizontalOstrowskiBlockErrorCap] using
    D.abs_horizontalOstrowskiRotationErrorPrefix_le_cap
      (D.horizontalOstrowskiDigits r) (r + 1)

/--
high orbit 上で使う block 全体の安全な shift budget。

pure Ostrowski composite error cap と、`r` steps 分の Collatz correction cap の和。
-/
noncomputable def horizontalOstrowskiBlockShiftBudget
    (D : BeattyRegularOstrowskiSystem)
    (r X : ℕ) : ℝ :=
  D.horizontalOstrowskiBlockErrorCap r +
    (r : ℝ) * collatzLogCorrectionCap X

end BeattyRegularOstrowskiSystem

/--
threshold `1` までの上側 margin が perturbation budget より大きければ、
absolute perturbation を加えても non-wrap 側 `base + perturbation < 1` を保つ。
-/
theorem nonwrap_stable_of_abs_perturbation_lt_margin
    {base perturbation budget : ℝ}
    (hAbs : |perturbation| ≤ budget)
    (hMargin : budget < 1 - base) :
    base + perturbation < 1 := by
  have hUpper : perturbation ≤ budget := (abs_le.mp hAbs).2
  linarith

/--
threshold `1` からの下側 margin が perturbation budget より大きければ、
absolute perturbation を加えても strict wrap 側 `1 < base + perturbation` を保つ。
-/
theorem wrap_stable_of_abs_perturbation_lt_margin
    {base perturbation budget : ℝ}
    (hAbs : |perturbation| ≤ budget)
    (hMargin : budget < base - 1) :
    1 < base + perturbation := by
  have hLower : -budget ≤ perturbation := (abs_le.mp hAbs).1
  linarith

end Bridge

namespace Runs

/--
任意 block length `r` の canonical horizontal Ostrowski decomposition を actual run へ接続する。

`oddSteps w = r` なら pure rotation の整数部分は fractional part から消え、
actual phase shift は exact に

`composite Ostrowski error + Collatz correction sum`

だけになる。
-/
theorem logPhase_horizontalOstrowskiBlock
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r +
          h.logCorrectionSum) := by
  rw [h.logPhase_run, hSteps]
  rw [D.horizontalOstrowskiBlock_decomposition r]
  calc
    Int.fract
        (Bridge.collatzLogPhase x +
          (((D.horizontalOstrowskiBlockInteger r : ℤ) : ℝ) +
            D.horizontalOstrowskiBlockError r) +
          h.logCorrectionSum) =
      Int.fract
        ((Bridge.collatzLogPhase x +
            D.horizontalOstrowskiBlockError r +
            h.logCorrectionSum) +
          ((D.horizontalOstrowskiBlockInteger r : ℤ) : ℝ)) := by
        congr 1
        ring
    _ = Int.fract
        (Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r +
          h.logCorrectionSum) := by
      rw [Int.fract_add_intCast]

/--
high orbit 上では actual block shift

`composite error + correction sum`

の absolute value を canonical Ostrowski error cap と correction cap の和で評価できる。
-/
theorem horizontalOstrowskiBlockShift_abs_le_budget
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x) :
    |D.horizontalOstrowskiBlockError r + h.logCorrectionSum| ≤
      D.horizontalOstrowskiBlockShiftBudget r X := by
  have hErr := D.abs_horizontalOstrowskiBlockError_le_cap r
  have hCorrNonneg := h.logCorrectionSum_nonneg
  have hCorr := h.logCorrectionSum_le_steps_mul_cap hX hAbove
  rw [hSteps] at hCorr
  have hTriangle :
      |D.horizontalOstrowskiBlockError r + h.logCorrectionSum| ≤
        |D.horizontalOstrowskiBlockError r| +
          |h.logCorrectionSum| :=
    abs_add_le _ _
  rw [abs_of_nonneg hCorrNonneg] at hTriangle
  calc
    |D.horizontalOstrowskiBlockError r + h.logCorrectionSum|
        ≤ |D.horizontalOstrowskiBlockError r| +
            h.logCorrectionSum := hTriangle
    _ ≤ D.horizontalOstrowskiBlockErrorCap r +
          (r : ℝ) * Bridge.collatzLogCorrectionCap X :=
      add_le_add hErr hCorr
    _ = D.horizontalOstrowskiBlockShiftBudget r X := rfl

/--
純 Ostrowski block が既に threshold `1` の wrap 側なら、
正の Collatz correction を加えても wrap 側から戻らない。

actual carry を定義しているわけではなく、unwrapped phase argument の側だけを述べる。
-/
theorem horizontalOstrowski_pureWrap_preserved
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hPureWrap :
      1 ≤ Bridge.collatzLogPhase x +
        D.horizontalOstrowskiBlockError r) :
    1 ≤ Bridge.collatzLogPhase x +
      D.horizontalOstrowskiBlockError r +
      h.logCorrectionSum := by
  have hCorr := h.logCorrectionSum_nonneg
  linarith

/--
純 Ostrowski block から threshold `1` までの margin が
Collatz correction より大きければ、
純 block 自身も strict non-wrap 側にあり、
actual unwrapped argument も non-wrap 側に留まる。
-/
theorem horizontalOstrowski_pureNonwrap_preserved
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hMargin :
      h.logCorrectionSum <
        1 - (Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r)) :
    Bridge.collatzLogPhase x +
        D.horizontalOstrowskiBlockError r +
        h.logCorrectionSum < 1 := by
  linarith

/--
high orbit 上の一様 correction bound だけで non-wrap preservation を判定する版。
-/
theorem horizontalOstrowski_pureNonwrap_preserved_of_cap
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x)
    (hMargin :
      (r : ℝ) * Bridge.collatzLogCorrectionCap X <
        1 - (Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r)) :
    Bridge.collatzLogPhase x +
        D.horizontalOstrowskiBlockError r +
        h.logCorrectionSum < 1 := by
  have hCorr := h.logCorrectionSum_le_steps_mul_cap hX hAbove
  rw [hSteps] at hCorr
  have hStrict :
      h.logCorrectionSum <
        1 - (Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r) :=
    lt_of_le_of_lt hCorr hMargin
  exact h.horizontalOstrowski_pureNonwrap_preserved D r hStrict

/--
block 全体の safe budget が開始 phase の両側 margin より小さければ、
actual unwrapped argument は strict に `(0,1)` 内に留まる。

従って fractional-part reduction は何も変えず、actual endpoint phase は

`start phase + composite Ostrowski error + correction sum`

そのものになる。
-/
theorem logPhase_horizontalOstrowskiBlock_eq_unwrapped_of_budget
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x)
    (hLowerMargin :
      D.horizontalOstrowskiBlockShiftBudget r X <
        Bridge.collatzLogPhase x)
    (hUpperMargin :
      D.horizontalOstrowskiBlockShiftBudget r X <
        1 - Bridge.collatzLogPhase x) :
    Bridge.collatzLogPhase y =
      Bridge.collatzLogPhase x +
        D.horizontalOstrowskiBlockError r +
        h.logCorrectionSum := by
  have hAbs :=
    h.horizontalOstrowskiBlockShift_abs_le_budget
      D r X hSteps hX hAbove
  have hBounds := abs_le.mp hAbs
  have hArgPos :
      0 < Bridge.collatzLogPhase x +
        (D.horizontalOstrowskiBlockError r + h.logCorrectionSum) := by
    linarith [hBounds.1]
  have hArgLt :
      Bridge.collatzLogPhase x +
        (D.horizontalOstrowskiBlockError r + h.logCorrectionSum) < 1 := by
    linarith [hBounds.2]
  rw [h.logPhase_horizontalOstrowskiBlock D r hSteps]
  have hFract :
      Int.fract
          (Bridge.collatzLogPhase x +
            D.horizontalOstrowskiBlockError r +
            h.logCorrectionSum) =
        Bridge.collatzLogPhase x +
          D.horizontalOstrowskiBlockError r +
          h.logCorrectionSum := by
    apply Int.fract_eq_self.2
    constructor
    · linarith
    · simpa [add_assoc] using hArgLt
  exact hFract

end Runs
end Collatz3
