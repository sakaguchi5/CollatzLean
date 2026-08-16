import CollatzLean.Collatz2.CSTMicro.Path

/-!
# General CST: weighted affine functional and capacity

binary path `P` だけから standard Collatz affine numerator

  2^k * y = 3^m * x + B(P)

の `B(P)` を構成する。

terminal contracting gap

  G(P) = 2^k - 3^m

に対して

  G(P) * x ≤ B(P)

が endpoint nondecrease `x ≤ y` と exact に対応する。
-/

namespace Collatz2
namespace CSTMicro

/--
standard parity word の affine correction numerator。

head parity を読む recursion:
* even: `B(0v) = 2 B(v)`
* odd : `B(1v) = 3^(ones v) + 2 B(v)`
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

/-- path が持つ whole affine equation。 -/
def AffineRealizes
    (v : ParityWord)
    (x y : ℕ) : Prop :=
  2 ^ v.length * y =
    3 ^ oddCount v * x + affineConst v

/--
parity word 自体の step-by-step exact trace。

`false` は `x = 2z`、
`true` は `3x+1 = 2z` を要求する。
-/
def TraceRealizes : ParityWord → ℕ → ℕ → Prop
  | [], x, y => x = y
  | false :: v, x, y =>
      ∃ z : ℕ, x = 2 * z ∧ TraceRealizes v z y
  | true :: v, x, y =>
      ∃ z : ℕ, 3 * x + 1 = 2 * z ∧ TraceRealizes v z y

/--
exact parity realization。

現在は trace と affine equation を lossless packet として同時に持つ。
後続で trace から affine equation を単独導出してもよい。
-/
def ExactRealizes
    (v : ParityWord)
    (x y : ℕ) : Prop :=
  TraceRealizes v x y ∧ AffineRealizes v x y

namespace ExactRealizes

theorem trace
    {v : ParityWord} {x y : ℕ}
    (h : ExactRealizes v x y) :
    TraceRealizes v x y :=
  h.1

theorem affine
    {v : ParityWord} {x y : ℕ}
    (h : ExactRealizes v x y) :
    AffineRealizes v x y :=
  h.2

end ExactRealizes

namespace FirstPassagePath

/--
Archimedean capacity の数値版。

`G = terminalGap > 0` に対して `B/G`。
-/
def capacity (P : FirstPassagePath) : ℕ :=
  affineConst P.word / P.terminalGap

/--
division を使わない exact capacity predicate。

`WithinCapacity P x` は `G*x ≤ B`。
-/
def WithinCapacity
    (P : FirstPassagePath)
    (x : ℕ) : Prop :=
  P.terminalGap * x ≤ affineConst P.word

/--
exact affine realization で endpoint が start 以上なら、
start は Archimedean capacity 内にある。
-/
theorem withinCapacity_of_affine_start_le_end
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    P.WithinCapacity x := by
  unfold AffineRealizes at h
  unfold WithinCapacity
  have hmul :
      2 ^ P.length * x ≤
        2 ^ P.length * y :=
    Nat.mul_le_mul_left (2 ^ P.length) hxy
  have h' :
      2 ^ P.length * y =
        3 ^ P.endpointOddCount * x +
          affineConst P.word := by
    simpa [length, endpointOddCount] using h
  rw [h'] at hmul
  have hsplit := P.twoPow_eq_threePow_add_terminalGap
  rw [hsplit, add_mul] at hmul
  omega

/--
capacity 内なら affine endpoint は start 以上。

これで `G*x ≤ B` と endpoint nondecrease が exact に対応する。
-/
theorem start_le_end_of_affine_withinCapacity
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hcap : P.WithinCapacity x) :
    x ≤ y := by
  unfold AffineRealizes at h
  unfold WithinCapacity at hcap
  have hsum :
      3 ^ P.endpointOddCount * x +
          P.terminalGap * x ≤
        3 ^ P.endpointOddCount * x +
          affineConst P.word :=
    Nat.add_le_add_left hcap _
  have hsplit := P.twoPow_eq_threePow_add_terminalGap
  have hmul :
      2 ^ P.length * x ≤
        2 ^ P.length * y := by
    calc
      2 ^ P.length * x
          =
          3 ^ P.endpointOddCount * x +
            P.terminalGap * x := by
              rw [hsplit, add_mul]
      _ ≤
          3 ^ P.endpointOddCount * x +
            affineConst P.word := hsum
      _ = 2 ^ P.length * y := h.symm
  have hpow : 0 < 2 ^ P.length :=
    Nat.pow_pos (by omega)
  by_contra hnot
  have hyx : y < x := by
    omega
  have hlt :
      2 ^ P.length * y <
        2 ^ P.length * x :=
    (Nat.mul_lt_mul_left hpow).2 hyx
  omega

/--
exact parity realization では endpoint nondecrease と
capacity predicate が同値。
-/
theorem start_le_end_iff_withinCapacity_of_exact
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : ExactRealizes P.word x y) :
    x ≤ y ↔ P.WithinCapacity x := by
  constructor
  · intro hxy
    exact
      withinCapacity_of_affine_start_le_end
        (P := P) h.affine hxy
  · intro hcap
    exact
      start_le_end_of_affine_withinCapacity
        (P := P) h.affine hcap

end FirstPassagePath
end CSTMicro
end Collatz2
