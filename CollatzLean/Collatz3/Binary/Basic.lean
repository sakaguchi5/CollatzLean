import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Collatz3 Binary: 二進語の最小核

二進表示は LSB-first の `List Bool` として扱う。

この層では Collatz の step / orbit は導入しない。
primitive data は

* 1 bit の自然数値、
* LSB-first 語の自然数値、
* 固定長表現、
* 通常の bit length の算術的条件、

だけに留める。
-/

namespace Collatz3
namespace Binary

/-- Bool bit を自然数 `0,1` に読む。 -/
def bitValue (b : Bool) : ℕ :=
  if b then 1 else 0

@[simp] theorem bitValue_false : bitValue false = 0 := rfl
@[simp] theorem bitValue_true : bitValue true = 1 := rfl

/--
LSB-first の二進語が表す自然数。

`b :: bs` は bit `b` を最下位に置き、残りを 1 bit 左へずらす。
-/
def valueLSB : List Bool → ℕ
  | [] => 0
  | b :: bs => bitValue b + 2 * valueLSB bs

@[simp] theorem valueLSB_nil : valueLSB [] = 0 := rfl

@[simp] theorem valueLSB_cons (b : Bool) (bs : List Bool) :
    valueLSB (b :: bs) = bitValue b + 2 * valueLSB bs := rfl

/--
LSB-first 語の append は、後半を前半の長さだけ左 shift する。
-/
theorem valueLSB_append (u v : List Bool) :
    valueLSB (u ++ v) =
      valueLSB u + 2 ^ u.length * valueLSB v := by
  induction u with
  | nil =>
      simp
  | cons b u ih =>
      simp only [List.cons_append, valueLSB_cons, List.length_cons]
      rw [ih, pow_succ]
      ring

/-- `m` 個の `1` は値 `2^m - 1`、という事実を減算なしで保持した形。 -/
theorem valueLSB_replicate_true_add_one (m : ℕ) :
    valueLSB (List.replicate m true) + 1 = 2 ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simp only [List.replicate_succ, valueLSB_cons, bitValue_true]
      calc
        1 + 2 * valueLSB (List.replicate m true) + 1
            = 2 * (valueLSB (List.replicate m true) + 1) := by ring
        _ = 2 * 2 ^ m := by rw [ih]
        _ = 2 ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- `m` 個の `0` の値は `0`。 -/
@[simp] theorem valueLSB_replicate_false (m : ℕ) :
    valueLSB (List.replicate m false) = 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

/-- 固定長 LSB-first 語が自然数 `x` を表す。 -/
def RepresentsAtLength
    (bits : List Bool)
    (x length : ℕ) : Prop :=
  bits.length = length ∧ valueLSB bits = x

namespace RepresentsAtLength

/-- 表現語の長さ。 -/
theorem length
    {bits : List Bool} {x length : ℕ}
    (h : RepresentsAtLength bits x length) :
    bits.length = length := h.1

/-- 表現語の値。 -/
theorem value
    {bits : List Bool} {x length : ℕ}
    (h : RepresentsAtLength bits x length) :
    valueLSB bits = x := h.2

end RepresentsAtLength

/--
通常の二進 bit length を算術的に特徴付ける薄い predicate。

実際の binary word の存在や一意性はここへ埋め込まない。
-/
def HasBitLength (x length : ℕ) : Prop :=
  0 < length ∧
    2 ^ (length - 1) ≤ x ∧
    x < 2 ^ length

namespace HasBitLength

/-- bit length は正。 -/
theorem pos
    {x length : ℕ}
    (h : HasBitLength x length) :
    0 < length := h.1

/-- bit length が与える下界。 -/
theorem lower
    {x length : ℕ}
    (h : HasBitLength x length) :
    2 ^ (length - 1) ≤ x := h.2.1

/-- bit length が与える上界。 -/
theorem upper
    {x length : ℕ}
    (h : HasBitLength x length) :
    x < 2 ^ length := h.2.2

end HasBitLength

end Binary
end Collatz3
