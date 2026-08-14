import CollatzLean.Collatz2.Geometry.Center
import CollatzLean.Collatz2.Canonical.SwapResidue
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Collatz2 Geometry: cyclic translation / center geometry

word `w` を cut `k` で

  w = u ++ v

と分けたとき cyclic rotation を `v ++ u` とする。
rotation は odd/two diagonal coefficients を保存するため、negative branch では
center gap も保存する。

特に `w = e :: v` の一文字 rotation `v ++ [e]` について、

  2^e * B(rot) = 3 * B(w) + G

が exact に成り立つ。center `Z=B/G` では

  2^e * Z(rot) = 3 * Z(w) + 1

という normalized Collatz recurrence になる。
-/

namespace Collatz2
namespace Word

/-- cut `k` による cyclic rotation。 -/
def cyclicRotate (w : Word) (k : ℕ) : Word :=
  w.drop k ++ w.take k

/-- cyclic rotation は odd-step 数を保存する。 -/
theorem oddSteps_cyclicRotate
    (w : Word)
    (k : ℕ) :
    oddSteps (cyclicRotate w k) = oddSteps w := by
  have h := congrArg oddSteps (List.take_append_drop k w)
  simp only [oddSteps_append] at h
  unfold cyclicRotate
  rw [oddSteps_append]
  omega

/-- cyclic rotation は total two-depth を保存する。 -/
theorem twoSteps_cyclicRotate
    (w : Word)
    (k : ℕ) :
    twoSteps (cyclicRotate w k) = twoSteps w := by
  have h := congrArg twoSteps (List.take_append_drop k w)
  simp only [twoSteps_append] at h
  unfold cyclicRotate
  rw [twoSteps_append]
  omega

/-- cyclic rotation は signed determinant を保存する。 -/
theorem determinant_cyclicRotate
    (w : Word)
    (k : ℕ) :
    (AffineTransfer.ofWord (cyclicRotate w k)).determinant =
      (AffineTransfer.ofWord w).determinant := by
  rw [AffineTransfer.determinant_ofWord, AffineTransfer.determinant_ofWord,
    oddSteps_cyclicRotate, twoSteps_cyclicRotate]

/-- cyclic rotation は negative branch の natural center gap を保存する。 -/
theorem centerGap_cyclicRotate
    (w : Word)
    (k : ℕ) :
    (AffineTransfer.ofWord (cyclicRotate w k)).centerGap =
      (AffineTransfer.ofWord w).centerGap := by
  unfold AffineTransfer.centerGap
  simp only [AffineTransfer.ofWord_twoCoeff, AffineTransfer.ofWord_oddCoeff]
  rw [oddSteps_cyclicRotate, twoSteps_cyclicRotate]

/-- nonempty word の一文字 left rotation。 -/
def rotateOne : Word → Word
  | [] => []
  | e :: v => v ++ [e]

@[simp] theorem rotateOne_cons (e : ℕ) (v : Word) :
    rotateOne (e :: v) = v ++ [e] := rfl

/-- 一文字 rotation は general cyclic rotation `k=1` と一致する。 -/
theorem rotateOne_eq_cyclicRotate_one
    (e : ℕ)
    (v : Word) :
    rotateOne (e :: v) = cyclicRotate (e :: v) 1 := by
  simp [rotateOne, cyclicRotate]

/--
negative word の一文字 rotation translation recurrence。
center division をする前の lossless 版。
-/
theorem twoPow_mul_affineConst_rotateOne
    {e : ℕ}
    {v : Word}
    (hC : Contracting (e :: v)) :
    2 ^ e * affineConst (v ++ [e]) =
      3 * affineConst (e :: v) +
        (AffineTransfer.ofWord (e :: v)).centerGap := by
  have hPow :
      3 ^ oddSteps (e :: v) < 2 ^ twoSteps (e :: v) :=
    (contracting_iff_threePow_lt_twoPow).1 hC
  have hGap :
      (AffineTransfer.ofWord (e :: v)).centerGap +
          3 ^ oddSteps (e :: v) =
        2 ^ twoSteps (e :: v) := by
    unfold AffineTransfer.centerGap
    simp only [AffineTransfer.ofWord_twoCoeff, AffineTransfer.ofWord_oddCoeff]
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hRot := affineConst_append v ([e] : Word)
  simp only [oddSteps, List.length_cons, List.length_nil, zero_add, pow_one, twoSteps,
    affineConst, pow_zero, mul_zero,add_zero, mul_one] at hRot
  simp only [affineConst_cons]
  rw [hRot]
  simp only [oddSteps_cons, twoSteps_cons] at hGap
  rw [pow_add] at hGap
  rw [pow_succ] at hGap
  ring_nf at hGap ⊢
  have hGap' :
      (AffineTransfer.ofWord (e :: v)).centerGap +
          3 ^ v.oddSteps * 3 =
        2 ^ e * 2 ^ List.sum v := by
    simpa [twoSteps] using hGap
  rw [← hGap']
  ring

/-- negative word の projective center を rational number として読む。 -/
def negativeCenterQ (w : Word) : ℚ :=
  (affineConst w : ℚ) /
    ((AffineTransfer.ofWord w).centerGap : ℚ)

/-- cut `k` の cyclic center `Z_k`。 -/
def cyclicCenterQ (w : Word) (k : ℕ) : ℚ :=
  negativeCenterQ (cyclicRotate w k)

/-- `Z_0` は original center。 -/
@[simp] theorem cyclicCenterQ_zero (w : Word) :
    cyclicCenterQ w 0 = negativeCenterQ w := by
  simp [cyclicCenterQ, cyclicRotate]

/-- 一文字 rotation でも center gap は同じ。 -/
theorem centerGap_rotateOne
    (e : ℕ)
    (v : Word) :
    (AffineTransfer.ofWord (rotateOne (e :: v))).centerGap =
      (AffineTransfer.ofWord (e :: v)).centerGap := by
  rw [rotateOne_eq_cyclicRotate_one]
  exact centerGap_cyclicRotate (e :: v) 1

/--
cyclic centers は exact normalized Collatz recurrence を満たす。

  2^e * Z(rot) = 3*Z + 1.
-/
theorem negativeCenterQ_rotateOne_recurrence
    {e : ℕ}
    {v : Word}
    (hC : Contracting (e :: v)) :
    (2 ^ e : ℚ) * negativeCenterQ (rotateOne (e :: v)) =
      3 * negativeCenterQ (e :: v) + 1 := by
  have hGpos :
      0 < (AffineTransfer.ofWord (e :: v)).centerGap :=
    AffineTransfer.centerGap_pos_of_negative hC
  have hGne :
      (((AffineTransfer.ofWord (e :: v)).centerGap : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hGpos)
  have hTrans := twoPow_mul_affineConst_rotateOne hC
  unfold negativeCenterQ
  rw [centerGap_rotateOne]
  field_simp [hGne]
  exact_mod_cast hTrans


/--
二つの actual run `u : S -> X`, `v : X -> T` を cyclic swap したときの
translation 差の全 cut exact identity。

`T = S + 2*n` とすると

  B(v++u)-B(u++v)
    = 2*n*3^|u|*(2^H(v)-3^|v|)
      +(2^H(u++v)-3^|u++v|)*(X-T).

current endpoint-floor object では両右辺項が strict positive になる。
-/
theorem cyclicTranslate_sub_exact
    {u v : Word}
    {S X T n : ℕ}
    (hu : Realizes u S X)
    (hv : Realizes v X T)
    (hST : T = S + 2 * n) :
    ((affineConst (v ++ u) : ℕ) : ℤ) -
        ((affineConst (u ++ v) : ℕ) : ℤ) =
      (2 * n : ℤ) * ((3 : ℤ) ^ oddSteps u) *
          (((2 : ℤ) ^ twoSteps v) - ((3 : ℤ) ^ oddSteps v)) +
        (((2 : ℤ) ^ twoSteps (u ++ v)) -
            ((3 : ℤ) ^ oddSteps (u ++ v))) *
          ((X : ℤ) - (T : ℤ)) := by
  have huNat := (realizes_iff u S X).1 hu
  have hvNat := (realizes_iff v X T).1 hv
  have huZ :
      ((2 : ℤ) ^ twoSteps u) * (X : ℤ) =
        ((3 : ℤ) ^ oddSteps u) * (S : ℤ) +
          (affineConst u : ℤ) := by
    exact_mod_cast huNat
  have hvZ :
      ((2 : ℤ) ^ twoSteps v) * (T : ℤ) =
        ((3 : ℤ) ^ oddSteps v) * (X : ℤ) +
          (affineConst v : ℤ) := by
    exact_mod_cast hvNat
  have hSTZ :
      (T : ℤ) = (S : ℤ) + 2 * (n : ℤ) := by
    exact_mod_cast hST
  rw [affineConst_append, affineConst_append,
    twoSteps_append, oddSteps_append, pow_add, pow_add]
  push_cast
  linear_combination
    -((((2 : ℤ) ^ twoSteps v) - ((3 : ℤ) ^ oddSteps v))) * huZ
    -((((3 : ℤ) ^ oddSteps u) - ((2 : ℤ) ^ twoSteps u))) * hvZ
    + (((3 : ℤ) ^ oddSteps u) *
        (((2 : ℤ) ^ twoSteps v) - ((3 : ℤ) ^ oddSteps v))) * hSTZ

end Word
end Collatz2
