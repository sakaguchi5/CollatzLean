import CollatzLean.Collatz3.CSTMicro.Residue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Collatz3 CSTMicro: affine equation と exact parity trace の一致

Stage 1 では exact trace から whole affine equation を導いた。
ここでは逆向きを証明し、standard parity word について

  TraceRealizes v x y ↔ AffineRealizes v x y

を閉じる。

さらに parity cylinder の最小代表から canonical endpoint を定義し、
その組が実際に exact parity trace を実現することを theorem として導く。
realization witness を structure field として保存しない。
-/

namespace Collatz3
namespace CSTMicro

/-- whole affine equation は step-by-step parity trace を一意に復元する。 -/
theorem AffineRealizes.trace
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    TraceRealizes v x y := by
  induction v generalizing x with
  | nil =>
      have hxy : x = y := by
        symm
        simpa [AffineRealizes] using h
      simp only [TraceRealizes, hxy]
  | cons b v ih =>
      cases b with
      | false =>
          have hEq :
              2 ^ v.length * 2 * y =
                3 ^ oddCount v * x + 2 * affineConst v := by
            simpa only [AffineRealizes,List.length_cons, oddCount_false_cons,
              affineConst_false_cons, pow_succ] using h
          obtain ⟨q, hxEven | hxOdd⟩ := x.even_or_odd'
          · refine ⟨q, hxEven, ih ?_⟩
            unfold AffineRealizes
            have hTwo :
                2 * (2 ^ v.length * y) =
                  2 * (3 ^ oddCount v * q + affineConst v) := by
              calc
                2 * (2 ^ v.length * y)
                    = 2 ^ v.length * 2 * y := by ring
                _ = 3 ^ oddCount v * x + 2 * affineConst v := hEq
                _ = 2 * (3 ^ oddCount v * q + affineConst v) := by
                      rw [hxEven]
                      ring
            exact Nat.mul_left_cancel (by decide : 0 < (2 : ℕ)) hTwo
          · have hOddPow : Odd (3 ^ oddCount v) :=
              (show Odd (3 : ℕ) by decide).pow
            rcases hOddPow with ⟨r, hr⟩
            rw [hxOdd, hr] at hEq
            ring_nf at hEq
            omega
      | true =>
          have hEq :
              2 ^ v.length * 2 * y =
                3 ^ oddCount v * (3 * x + 1) +
                  2 * affineConst v := by
            have hRaw :
                2 ^ v.length * 2 * y =
                  (3 ^ oddCount v * 3) * x +
                    (3 ^ oddCount v + 2 * affineConst v) := by
              simpa only [AffineRealizes,List.length_cons, oddCount_true_cons,
                affineConst_true_cons, pow_succ] using h
            calc
              2 ^ v.length * 2 * y
                  = (3 ^ oddCount v * 3) * x +
                      (3 ^ oddCount v + 2 * affineConst v) := hRaw
              _ = 3 ^ oddCount v * (3 * x + 1) +
                    2 * affineConst v := by ring
          obtain ⟨q, hxEven | hxOdd⟩ := x.even_or_odd'
          · have hOddPow : Odd (3 ^ oddCount v) :=
              (show Odd (3 : ℕ) by decide).pow
            rcases hOddPow with ⟨r, hr⟩
            rw [hxEven, hr] at hEq
            ring_nf at hEq
            omega
          · let z : ℕ := 3 * q + 2
            have hxz : 3 * x + 1 = 2 * z := by
              dsimp [z]
              rw [hxOdd]
              ring
            refine ⟨z, hxz, ih ?_⟩
            unfold AffineRealizes
            have hTwo :
                2 * (2 ^ v.length * y) =
                  2 * (3 ^ oddCount v * z + affineConst v) := by
              calc
                2 * (2 ^ v.length * y)
                    = 2 ^ v.length * 2 * y := by ring
                _ = 3 ^ oddCount v * (3 * x + 1) +
                      2 * affineConst v := hEq
                _ = 2 * (3 ^ oddCount v * z + affineConst v) := by
                      rw [hxz]
                      ring
            exact Nat.mul_left_cancel (by decide : 0 < (2 : ℕ)) hTwo

/-- standard parity word では exact trace と whole affine equation は同値。 -/
theorem traceRealizes_iff_affineRealizes
    (v : ParityWord) (x y : ℕ) :
    TraceRealizes v x y ↔ AffineRealizes v x y := by
  constructor
  · exact TraceRealizes.affine
  · exact AffineRealizes.trace

/-- parity cylinder 最小代表に対応する canonical endpoint。 -/
def canonicalEndpoint (v : ParityWord) : ℕ :=
  (3 ^ oddCount v * leastRepresentative v + affineConst v) /
    parityModulus v

/--
parity cylinder 最小代表の affine numerator は modulus で割り切れる。
-/
theorem canonicalNumerator_mod_parityModulus
    (v : ParityWord) :
    (3 ^ oddCount v * leastRepresentative v + affineConst v) %
        parityModulus v = 0 := by
  have hModNe : parityModulus v ≠ 0 := by
    unfold parityModulus
    positivity
  let : NeZero (parityModulus v) :=
    ⟨hModNe⟩
  have hCastR :
      ((leastRepresentative v : ℕ) : ZMod (parityModulus v)) =
        parityStartClass v := by
    unfold leastRepresentative
    exact ZMod.natCast_zmod_val (parityStartClass v)
  have hSpec := parityStartClass_spec v
  rw [← hCastR] at hSpec
  have hZero :
      (((3 ^ oddCount v * leastRepresentative v + affineConst v : ℕ) :
          ZMod (parityModulus v))) = 0 := by
    simpa using hSpec
  have hDvd :
      parityModulus v ∣
        3 ^ oddCount v * leastRepresentative v + affineConst v :=
    (ZMod.natCast_eq_zero_iff
      (3 ^ oddCount v * leastRepresentative v + affineConst v)
      (parityModulus v)).1 hZero
  exact Nat.mod_eq_zero_of_dvd hDvd

/-- 最小代表と canonical endpoint は whole affine equation を満たす。 -/
theorem canonicalEndpoint_affine
    (v : ParityWord) :
    AffineRealizes v (leastRepresentative v) (canonicalEndpoint v) := by
  unfold AffineRealizes canonicalEndpoint parityModulus
  let N := 3 ^ oddCount v * leastRepresentative v + affineConst v
  have hMod : N % 2 ^ v.length = 0 := by
    simpa [N, parityModulus] using canonicalNumerator_mod_parityModulus v
  have hDecomp := Nat.mod_add_div N (2 ^ v.length)
  rw [hMod] at hDecomp
  simp only [zero_add] at hDecomp
  simpa [N, Nat.mul_comm] using hDecomp

/-- 最小代表と canonical endpoint は実際の step-by-step parity trace を実現する。 -/
theorem canonicalEndpoint_trace
    (v : ParityWord) :
    TraceRealizes v (leastRepresentative v) (canonicalEndpoint v) :=
  (canonicalEndpoint_affine v).trace

end CSTMicro
end Collatz3
