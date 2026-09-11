import CollatzLean.Collatz3.Semantics.OddStep
import CollatzLean.Collatz3.Bridge.Experimental2BeattyLog
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Collatz3 Bridge: actual odd-only Collatz の log₂ 位相

odd-only 一歩

`2^e * y = 3*x + 1`

を実数対数へ移す。ここで primitive に保存する解析座標は二つだけである。

* `collatzLogRotation = log₂(3/2)`：正規化 Beatty roof と共通の回転角。
* `collatzLogCorrection x = log₂(1 + 1/(3x))`：`+1` に由来する正の補正。

actual orbit の位相は

`collatzLogPhase x = fract(log₂ x)`

とする。一歩の 2 除算指数 `e` は log の整数部分にだけ現れるため、fractional part を取ると消える。
このファイルでは exact identity と exact phase update だけを証明し、補正項の大小評価は
`CollatzLogPhaseBounds` に分離する。
-/

namespace Collatz3
namespace Bridge

/-- actual Collatz log 位相で現れる一歩の無理回転角 `log₂(3/2)`。 -/
noncomputable def collatzLogRotation : ℝ :=
  Real.logb 2 ((3 : ℝ) / 2)

/-- `+1` に由来する一歩の正の対数補正。 -/
noncomputable def collatzLogCorrection (x : ℕ) : ℝ :=
  Real.logb 2 (1 + 1 / ((3 : ℝ) * (x : ℝ)))

/-- 初期値・軌道値を `log₂` の fractional part へ送る位相座標。 -/
noncomputable def collatzLogPhase (x : ℕ) : ℝ :=
  Int.fract (Real.logb 2 (x : ℝ))

/-- 回転角は既存の正規化 Beatty slope と同じ `log₂ 3 - 1`。 -/
theorem collatzLogRotation_eq_logb_three_sub_one :
    collatzLogRotation = Real.logb 2 3 - 1 := by
  exact logb_two_three_div_two

/-- log 位相は常に半開区間 `[0,1)` に入る。 -/
theorem collatzLogPhase_mem_Ico (x : ℕ) :
    0 ≤ collatzLogPhase x ∧ collatzLogPhase x < 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

end Bridge

namespace OddStep

/-- actual odd-only step の始点は正。 -/
theorem start_pos {e x y : ℕ} (h : OddStep e x y) : 0 < x := by
  rcases h.start_odd with ⟨k, hk⟩
  omega

/-- actual odd-only step の終点は正。 -/
theorem end_pos {e x y : ℕ} (h : OddStep e x y) : 0 < y := by
  rcases h.end_odd with ⟨k, hk⟩
  omega

/--
actual odd-only 一歩の exact log identity。

`2^e y = 3x+1` を

`3x+1 = 3x * (1 + 1/(3x))`

と分解して base 2 の対数を取る。
-/
theorem logb_end_eq_start_add_logb_three_sub_exponent_add_correction
    {e x y : ℕ}
    (h : OddStep e x y) :
    Real.logb 2 (y : ℝ) =
      Real.logb 2 (x : ℝ) + Real.logb 2 3 - (e : ℝ) +
        Bridge.collatzLogCorrection x := by
  have hxPos : 0 < x := h.start_pos
  have hyPos : 0 < y := h.end_pos
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxPos
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hyPos
  have hThreeX : (0 : ℝ) < (3 : ℝ) * (x : ℝ) := by positivity
  have hPow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hNum : (0 : ℝ) < (3 : ℝ) * (x : ℝ) + 1 := by positivity
  have hCorrArg :
      (0 : ℝ) < 1 + 1 / ((3 : ℝ) * (x : ℝ)) := by positivity
  have hEqR :
      (2 : ℝ) ^ e * (y : ℝ) =
        (3 : ℝ) * (x : ℝ) + 1 := by
    exact_mod_cast h.equation
  have hyEq :
      (y : ℝ) =
        ((3 : ℝ) * (x : ℝ) + 1) / (2 : ℝ) ^ e := by
    apply (eq_div_iff hPow.ne').2
    calc
      (y : ℝ) * (2 : ℝ) ^ e =
          (2 : ℝ) ^ e * (y : ℝ) := by ring
      _ = (3 : ℝ) * (x : ℝ) + 1 := hEqR
  have hFactor :
      (3 : ℝ) * (x : ℝ) + 1 =
        ((3 : ℝ) * (x : ℝ)) *
          (1 + 1 / ((3 : ℝ) * (x : ℝ))) := by
    field_simp [hThreeX.ne']
  calc
    Real.logb 2 (y : ℝ) =
        Real.logb 2
          (((3 : ℝ) * (x : ℝ) + 1) / (2 : ℝ) ^ e) := by
            rw [hyEq]
    _ = Real.logb 2 ((3 : ℝ) * (x : ℝ) + 1) -
          Real.logb 2 ((2 : ℝ) ^ e) := by
            exact Real.logb_div hNum.ne' hPow.ne'
    _ = Real.logb 2
          (((3 : ℝ) * (x : ℝ)) *
            (1 + 1 / ((3 : ℝ) * (x : ℝ)))) -
          Real.logb 2 ((2 : ℝ) ^ e) := by
            rw [hFactor]
    _ = (Real.logb 2 ((3 : ℝ) * (x : ℝ)) +
          Real.logb 2 (1 + 1 / ((3 : ℝ) * (x : ℝ)))) -
          Real.logb 2 ((2 : ℝ) ^ e) := by
            rw [Real.logb_mul hThreeX.ne' hCorrArg.ne']
    _ = ((Real.logb 2 3 + Real.logb 2 (x : ℝ)) +
          Bridge.collatzLogCorrection x) -
          ((e : ℝ) * Real.logb 2 2) := by
            rw [Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) hxR.ne']
            rw [Real.logb_pow]
            rfl
    _ = Real.logb 2 (x : ℝ) + Real.logb 2 3 - (e : ℝ) +
          Bridge.collatzLogCorrection x := by
            rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
            ring

/--
前定理を canonical rotation `log₂(3/2)` と整数 shift に分離した形。

最後の整数 shift は `1-e` なので fractional part では完全に消える。
-/
theorem logb_end_eq_rotation_add_integer
    {e x y : ℕ}
    (h : OddStep e x y) :
    Real.logb 2 (y : ℝ) =
      (Real.logb 2 (x : ℝ) + Bridge.collatzLogRotation +
        Bridge.collatzLogCorrection x) +
      (((1 : ℤ) - (e : ℤ) : ℤ) : ℝ) := by
  rw [h.logb_end_eq_start_add_logb_three_sub_exponent_add_correction]
  rw [Bridge.collatzLogRotation_eq_logb_three_sub_one]
  push_cast
  ring

/--
actual odd-only Collatz 一歩の exact log-phase update。

`e = v₂(3x+1)` に相当する指数は fractional part では消え、

`phase(y) = fract(phase(x) + log₂(3/2) + correction(x))`

だけが残る。
-/
theorem logPhase_step
    {e x y : ℕ}
    (h : OddStep e x y) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x + Bridge.collatzLogRotation +
          Bridge.collatzLogCorrection x) := by
  have hShift := h.logb_end_eq_rotation_add_integer
  unfold Bridge.collatzLogPhase
  rw [hShift]
  rw [Int.fract_add_intCast]
  have hFract :
      Int.fract
          ((Bridge.collatzLogRotation + Bridge.collatzLogCorrection x) +
            Real.logb 2 (x : ℝ)) =
        Int.fract
          ((Bridge.collatzLogRotation + Bridge.collatzLogCorrection x) +
            Int.fract (Real.logb 2 (x : ℝ))) := by
    let a : ℝ :=
      Bridge.collatzLogRotation + Bridge.collatzLogCorrection x
    let b : ℝ := Real.logb 2 (x : ℝ)
    calc
      Int.fract (a + b)
          = Int.fract
              (a + (((⌊b⌋ : ℤ) : ℝ) + Int.fract b)) := by
                rw [Int.floor_add_fract]
      _ = Int.fract
            ((a + Int.fract b) + ((⌊b⌋ : ℤ) : ℝ)) := by
              congr 1
              ring
      _ = Int.fract (a + Int.fract b) := by
            rw [Int.fract_add_intCast]
  simpa [add_assoc, add_comm, add_left_comm] using hFract

end OddStep
end Collatz3
