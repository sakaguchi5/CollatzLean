import CollatzLean.Collatz3.CSTMicro.Path
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTMicro: standard parity affine equation

binary parity word `v` から standard Collatz affine equation

  2^H * y = 3^p * x + B(v)

を構成する。

`TraceRealizes` は step-by-step parity trace、`AffineRealizes` は whole endpoint equation。
whole affine equation を structure field として保存せず、trace から theorem として導く。
-/

namespace Collatz3
namespace CSTMicro

/--
standard parity word の affine correction numerator `B(v)`。

head recursion:
* even: `B(0v) = 2 B(v)`
* odd : `B(1v) = 3^(oddCount v) + 2 B(v)`
-/
def affineConst : ParityWord → ℕ
  | [] => 0
  | false :: v => 2 * affineConst v
  | true :: v => 3 ^ oddCount v + 2 * affineConst v

@[simp] theorem affineConst_nil :
    affineConst ([] : ParityWord) = 0 := rfl

@[simp] theorem affineConst_false_cons (v : ParityWord) :
    affineConst (false :: v) = 2 * affineConst v := rfl

@[simp] theorem affineConst_true_cons (v : ParityWord) :
    affineConst (true :: v) =
      3 ^ oddCount v + 2 * affineConst v := rfl

/-- parity word が持つ whole affine endpoint equation。 -/
def AffineRealizes
    (v : ParityWord) (x y : ℕ) : Prop :=
  2 ^ v.length * y =
    3 ^ oddCount v * x + affineConst v

/--
parity word の step-by-step exact trace。

`false` は `x = 2z`、`true` は `3x+1 = 2z` を要求する。
-/
def TraceRealizes : ParityWord → ℕ → ℕ → Prop
  | [], x, y => x = y
  | false :: v, x, y =>
      ∃ z : ℕ, x = 2 * z ∧ TraceRealizes v z y
  | true :: v, x, y =>
      ∃ z : ℕ, 3 * x + 1 = 2 * z ∧ TraceRealizes v z y

namespace TraceRealizes

/-- exact trace は whole affine endpoint equation を満たす。 -/
theorem affine
    {v : ParityWord} {x y : ℕ}
    (h : TraceRealizes v x y) :
    AffineRealizes v x y := by
  induction v generalizing x with
  | nil =>
      have hxy : x = y := by
        simpa [TraceRealizes] using h
      subst y
      simp [AffineRealizes]
  | cons b v ih =>
      cases b
      · rcases h with ⟨z, hx, hz⟩
        have hTail := ih hz
        unfold AffineRealizes at hTail ⊢
        simp only [List.length_cons, oddCount_false_cons,
          affineConst_false_cons, pow_succ]
        calc
          2 ^ v.length * 2 * y
              = 2 * (2 ^ v.length * y) := by ring
          _ = 2 * (3 ^ oddCount v * z + affineConst v) := by rw [hTail]
          _ = 3 ^ oddCount v * (2 * z) + 2 * affineConst v := by ring
          _ = 3 ^ oddCount v * x + 2 * affineConst v := by rw [hx]
      · rcases h with ⟨z, hx, hz⟩
        have hTail := ih hz
        unfold AffineRealizes at hTail ⊢
        simp only [List.length_cons, oddCount_true_cons,
          affineConst_true_cons, pow_succ]
        calc
          2 ^ v.length * 2 * y
              = 2 * (2 ^ v.length * y) := by ring
          _ = 2 * (3 ^ oddCount v * z + affineConst v) := by rw [hTail]
          _ = 3 ^ oddCount v * (2 * z) + 2 * affineConst v := by ring
          _ = 3 ^ oddCount v * (3 * x + 1) + 2 * affineConst v := by rw [← hx]
          _ = (3 ^ oddCount v * 3) * x +
                (3 ^ oddCount v + 2 * affineConst v) := by ring

end TraceRealizes

end CSTMicro
end Collatz3
