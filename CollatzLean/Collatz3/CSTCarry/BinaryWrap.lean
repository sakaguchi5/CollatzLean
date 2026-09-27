import Mathlib.Tactic.NormNum

/-!
# Collatz3 CSTCarry: fixed-width binary wrap

`H` bit の canonical residue に shift を足すとき、`2^H` を越えるかどうかだけを
独立した算術 object として切り出す。

これは Ferrers deformation の residue shift を受け取る側の最小層であり、
Collatz 固有の定義は一切持たない。
-/

namespace Collatz3
namespace CSTCarry

/-- `H` bit residue 上の一回の shift。両者を標準代表 `0 .. 2^H-1` に取る。 -/
structure BinaryShiftData (H : ℕ) where
  boundary : ℕ
  shift : ℕ
  boundary_lt : boundary < 2 ^ H
  shift_lt : shift < 2 ^ H

namespace BinaryShiftData

/-- 固定幅 modulus。 -/
def modulus {H : ℕ} (_ : BinaryShiftData H) : ℕ :=
  2 ^ H

/-- boundary から modulus まで残っている距離。 -/
def threshold {H : ℕ} (X : BinaryShiftData H) : ℕ :=
  X.modulus - X.boundary

/-- `H+1` bit 目へ carry が出る、すなわち fixed-width overflow が起こる。 -/
def Wraps {H : ℕ} (X : BinaryShiftData H) : Prop :=
  X.modulus ≤ X.boundary + X.shift

/-- shift 後の canonical residue。 -/
def representative {H : ℕ} (X : BinaryShiftData H) : ℕ :=
  (X.boundary + X.shift) % X.modulus

/-- wrap は「shift が残り距離以上」と exact に同値。 -/
theorem wraps_iff_shift_ge_threshold
    {H : ℕ}
    (X : BinaryShiftData H) :
    X.Wraps ↔ X.threshold ≤ X.shift := by
  unfold Wraps threshold modulus
  omega

/-- 二つの標準代表の和なので、overflow は高々一周である。 -/
theorem sum_lt_two_mul_modulus
    {H : ℕ}
    (X : BinaryShiftData H) :
    X.boundary + X.shift < 2 * X.modulus := by
  have hb : X.boundary < 2 ^ H := X.boundary_lt
  have hs : X.shift < 2 ^ H := X.shift_lt
  unfold modulus
  omega

/-- wrap が無ければ canonical residue は普通の整数加算そのもの。 -/
theorem representative_eq_add_of_not_wrap
    {H : ℕ}
    (X : BinaryShiftData H)
    (h : ¬ X.Wraps) :
    X.representative = X.boundary + X.shift := by
  unfold representative Wraps modulus at *
  apply Nat.mod_eq_of_lt
  omega

/-- wrap が起きれば、高々一周なので modulus を一回引くだけでよい。 -/
theorem representative_eq_sub_modulus_of_wrap
    {H : ℕ}
    (X : BinaryShiftData H)
    (h : X.Wraps) :
    X.representative = X.boundary + X.shift - X.modulus := by
  have hLower : X.modulus ≤ X.boundary + X.shift := h
  have hUpper : X.boundary + X.shift < 2 * X.modulus :=
    X.sum_lt_two_mul_modulus
  have hSubLt :
      X.boundary + X.shift - X.modulus < X.modulus := by
    omega
  have hDecomp :
      X.boundary + X.shift =
        (X.boundary + X.shift - X.modulus) + X.modulus := by
    omega
  unfold representative
  rw [hDecomp, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hSubLt]

/--
59 と 76 を 7 bit で足すと 135 になり、128 を一回越える。
前節で使った具体例を executable certificate として残す。
-/
theorem example_7bit_wrap :
    let X : BinaryShiftData 7 :=
      { boundary := 59
        shift := 76
        boundary_lt := by norm_num
        shift_lt := by norm_num }
    X.Wraps ∧ X.threshold = 69 ∧ X.representative = 7 := by
  norm_num [Wraps, threshold, representative, modulus]

end BinaryShiftData
end CSTCarry
end Collatz3
