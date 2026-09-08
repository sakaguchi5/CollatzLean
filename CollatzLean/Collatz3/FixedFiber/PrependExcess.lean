import CollatzLean.Collatz3.FixedFiber.UniversalExcess

/-!
# Collatz3: 先頭指数を付けたときの fixed-fiber excess

ここは pure fixed-fiber arithmetic のみを扱う。
actual `Runs` / `BackwardStep` / predecessor semantics は import しない。

signed `E_RF` を正本として、先頭指数 `e` を付けたときの中心化座標を

`C_Z(e,w) = E_RF^Z(e::w) + 2 D_q`

で定義する。ただし `q = oddSteps w`, `D_q = 3^q - 2^q`。

核心は raw Word 全体で

`C_Z(e,w) = 2^e * affineConst w`

であり、したがって

`C_Z(e+2,w) = 4 * C_Z(e,w)`

が仮定なしに成立する。

Nat-valued `prependExcessCoordinate` は valid word 用の互換 view として残す。
actual 逆コラッツ木との接続は `Bridge.PredecessorExcess` で行う。
-/

namespace Collatz3
namespace Word

/--
signed `E_RF` による先頭付加中心化座標。

raw Word に対しても符号情報を失わない正本。
-/
def signedPrependExcessCoordinate
    (e : ℕ)
    (w : Word) : ℤ :=
  signedUniversalExcess (e :: w) +
    2 * signedFixedFiberBaseline (oddSteps w)

/--
signed 中心化座標の exact 基本式。

`C_Z(e,w) = 2^e * affineConst w`

validity や `e>0` を必要としない。
-/
theorem signedPrependExcessCoordinate_eq_twoPow_mul_affineConst
    (e : ℕ)
    (w : Word) :
    signedPrependExcessCoordinate e w =
      (2 : ℤ) ^ e * (affineConst w : ℤ) := by
  unfold signedPrependExcessCoordinate signedUniversalExcess
  rw [oddSteps_cons, affineConst_cons, signedFixedFiberBaseline_succ]
  simp only [
    Nat.cast_add,
    Nat.cast_mul,
    Nat.cast_pow,
    Nat.cast_ofNat
  ]
  ring

/--
signed `E_RF` 自身の先頭付加更新則。

`q = oddSteps w` とすると

`E_RF^Z(e::w)
 = 2^e E_RF^Z(w) + (2^e - 2) D_q`。
-/
theorem signedUniversalExcess_cons
    (e : ℕ)
    (w : Word) :
    signedUniversalExcess (e :: w) =
      (2 : ℤ) ^ e * signedUniversalExcess w +
        ((2 : ℤ) ^ e - 2) *
          signedFixedFiberBaseline (oddSteps w) := by
  unfold signedUniversalExcess
  rw [oddSteps_cons, affineConst_cons, signedFixedFiberBaseline_succ]
  simp only [
    Nat.cast_add,
    Nat.cast_mul,
    Nat.cast_pow,
    Nat.cast_ofNat
  ]
  ring

/--
指数を `e` から `e+2` へ増やすと、
signed 中心化座標は raw Word 全体で exact に 4 倍。
-/
theorem signedPrependExcessCoordinate_add_two
    (e : ℕ)
    (w : Word) :
    signedPrependExcessCoordinate (e + 2) w =
      4 * signedPrependExcessCoordinate e w := by
  rw [
    signedPrependExcessCoordinate_eq_twoPow_mul_affineConst,
    signedPrependExcessCoordinate_eq_twoPow_mul_affineConst
  ]
  rw [pow_add]
  norm_num
  ring

/--
従来互換の Nat-valued 中心化座標。

valid tail と正指数の範囲では signed 正本の Nat view と一致する。
-/
def prependExcessCoordinate (e : ℕ) (w : Word) : ℕ :=
  universalExcess (e :: w) +
    2 * fixedFiberBaseline (oddSteps w)

/--
valid tail と正指数では signed 中心化座標は Nat view の exact cast。
-/
theorem signedPrependExcessCoordinate_eq_natCast
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    signedPrependExcessCoordinate e w =
      (prependExcessCoordinate e w : ℤ) := by
  have hConsValid : Valid (e :: w) := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact he
    · exact hValid a ha
  unfold signedPrependExcessCoordinate prependExcessCoordinate
  rw [signedUniversalExcess_eq_natCast hConsValid]
  rw [signedFixedFiberBaseline_eq_natCast]
  simp only [
    Nat.cast_add,
    Nat.cast_mul,
    Nat.cast_ofNat
  ]

/--
valid tail `w` の先頭に正指数 `e` を付けると、
Nat 中心化座標は `2^e * affineConst w` に exact に一致する。
-/
theorem prependExcessCoordinate_eq_twoPow_mul_affineConst
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate e w =
      2 ^ e * affineConst w := by
  have hConsValid : Valid (e :: w) := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact he
    · exact hValid a ha
  have hCons :=
    affineConst_eq_fixedFiberBaseline_add_universalExcess hConsValid
  have hAffine := affineConst_cons e w
  have hBase := fixedFiberBaseline_succ (oddSteps w)
  unfold prependExcessCoordinate
  rw [oddSteps_cons] at hCons
  omega

/--
Nat 中心化座標を tail の `E_RF` だけで書いた形。

`E_RF(e::w) + 2 D_q
 = 2^e (E_RF(w) + D_q)`。
-/
theorem prependExcessCoordinate_eq_twoPow_mul_excess_add_baseline
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate e w =
      2 ^ e *
        (universalExcess w + fixedFiberBaseline (oddSteps w)) := by
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e) (w := w) he hValid]
  rw [affineConst_eq_fixedFiberBaseline_add_universalExcess hValid]
  ring

/--
Nat `E_RF` の先頭付加更新則。

`E_RF(e::w)
 = 2^e E_RF(w) + (2^e - 2) D_q`。
-/
theorem universalExcess_cons
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    universalExcess (e :: w) =
      2 ^ e * universalExcess w +
        (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) := by
  have hCenter :=
    prependExcessCoordinate_eq_twoPow_mul_affineConst
      (e := e) (w := w) he hValid
  have hTail :=
    affineConst_eq_fixedFiberBaseline_add_universalExcess hValid
  have hTwo : 2 ≤ 2 ^ e :=
    two_le_twoPow_of_pos he
  have hScale :
      2 ^ e * fixedFiberBaseline (oddSteps w) =
        (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) +
          2 * fixedFiberBaseline (oddSteps w) := by
    calc
      2 ^ e * fixedFiberBaseline (oddSteps w) =
          ((2 ^ e - 2) + 2) * fixedFiberBaseline (oddSteps w) := by
            rw [Nat.sub_add_cancel hTwo]
      _ =
          (2 ^ e - 2) * fixedFiberBaseline (oddSteps w) +
            2 * fixedFiberBaseline (oddSteps w) := by
              ring
  have hEq :
      universalExcess (e :: w) +
          2 * fixedFiberBaseline (oddSteps w) =
        (2 ^ e * universalExcess w +
            (2 ^ e - 2) * fixedFiberBaseline (oddSteps w)) +
          2 * fixedFiberBaseline (oddSteps w) := by
    change prependExcessCoordinate e w = _
    rw [hCenter, hTail, Nat.mul_add, hScale]
    ring
  exact Nat.add_right_cancel hEq

/-- 指数 `1` を先頭へ付けると Nat `E_RF` は exact に 2 倍。 -/
theorem universalExcess_one_cons
    {w : Word}
    (hValid : Valid w) :
    universalExcess (1 :: w) =
      2 * universalExcess w := by
  simpa using
    (universalExcess_cons (e := 1) (w := w) (by decide) hValid)

/--
valid tail では Nat 中心化座標も `e ↦ e+2` で exact に 4 倍。

数学的正本は `signedPrependExcessCoordinate_add_two`。
-/
theorem prependExcessCoordinate_add_two
    {e : ℕ}
    {w : Word}
    (he : 0 < e)
    (hValid : Valid w) :
    prependExcessCoordinate (e + 2) w =
      4 * prependExcessCoordinate e w := by
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e + 2) (w := w) (by omega) hValid]
  rw [prependExcessCoordinate_eq_twoPow_mul_affineConst
        (e := e) (w := w) he hValid]
  rw [pow_add]
  norm_num
  ring

end Word
end Collatz3
