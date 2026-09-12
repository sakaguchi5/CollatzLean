import CollatzLean.Collatz3.CSTMicro.FirstPassageArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTMicro: Archimedean capacity and single-lift reduction

first-passage gap

  D = 2^H - 3^p > 0

に対して endpoint nondecrease `x ≤ y` は

  D * x ≤ B

と exact に同値になる。

さらに sharpened bound `B ≤ p * 3^(p-1)` と
純整数論入力

  p < 3D

を組み合わせると、非下降 start は modulus `2^H` 未満となる。
したがって parity cylinder の最小代表以外の higher lift はすべて排除される。

`p < 3D` 自体は Collatz combinatorics ではなく純粋な 2--3 冪差問題なので、
この第1段階では axiom にせず theorem の明示的な仮定として残す。
-/

namespace Collatz3
namespace CSTMicro
namespace FirstPassagePath

/-- numerical Archimedean capacity `B / D`。 -/
def capacity (P : FirstPassagePath) : ℕ :=
  affineConst P.word / P.terminalGap

/-- division-free capacity predicate `D*x ≤ B`。 -/
def WithinCapacity (P : FirstPassagePath) (x : ℕ) : Prop :=
  P.terminalGap * x ≤ affineConst P.word

/-- affine realization で endpoint が start 以上なら start は capacity 内。 -/
theorem withinCapacity_of_affine_start_le_end
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    P.WithinCapacity x := by
  unfold AffineRealizes at h
  unfold WithinCapacity
  have hmul :
      2 ^ P.length * x ≤ 2 ^ P.length * y :=
    Nat.mul_le_mul_left (2 ^ P.length) hxy
  have h' :
      2 ^ P.length * y =
        3 ^ P.endpointOddCount * x + affineConst P.word := by
    simpa [length, endpointOddCount] using h
  rw [h'] at hmul
  have hsplit := P.twoPow_eq_threePow_add_terminalGap
  rw [hsplit, add_mul] at hmul
  omega

/-- capacity 内の affine realization は endpoint nondecrease。 -/
theorem start_le_end_of_affine_withinCapacity
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hcap : P.WithinCapacity x) :
    x ≤ y := by
  unfold AffineRealizes at h
  unfold WithinCapacity at hcap
  have hsum :
      3 ^ P.endpointOddCount * x + P.terminalGap * x ≤
        3 ^ P.endpointOddCount * x + affineConst P.word :=
    Nat.add_le_add_left hcap _
  have hsplit := P.twoPow_eq_threePow_add_terminalGap
  have hmul :
      2 ^ P.length * x ≤ 2 ^ P.length * y := by
    calc
      2 ^ P.length * x
          = 3 ^ P.endpointOddCount * x + P.terminalGap * x := by
              rw [hsplit, add_mul]
      _ ≤ 3 ^ P.endpointOddCount * x + affineConst P.word := hsum
      _ = 2 ^ P.length * y := h.symm
  have hpow : 0 < 2 ^ P.length := Nat.pow_pos (by decide)
  by_contra hnot
  have hyx : y < x := by omega
  have hlt : 2 ^ P.length * y < 2 ^ P.length * x :=
    (Nat.mul_lt_mul_left hpow).2 hyx
  omega

/-- affine realizationでは endpoint nondecrease と capacity predicate が exact に同値。 -/
theorem start_le_end_iff_withinCapacity_of_affine
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : AffineRealizes P.word x y) :
    x ≤ y ↔ P.WithinCapacity x := by
  constructor
  · exact P.withinCapacity_of_affine_start_le_end h
  · exact P.start_le_end_of_affine_withinCapacity h

/-- exact parity trace でも同じ endpoint nondecrease criterion が成立する。 -/
theorem start_le_end_iff_withinCapacity_of_trace
    {P : FirstPassagePath}
    {x y : ℕ}
    (h : TraceRealizes P.word x y) :
    x ≤ y ↔ P.WithinCapacity x :=
  P.start_le_end_iff_withinCapacity_of_affine h.affine

/--
sharpened `B` bound から single-lift を得るのに十分な純整数論条件。

`p < 3D` は `B < D * 3^p` を保証するちょうど自然な形である。
-/
def SingleLiftGapCondition (P : FirstPassagePath) : Prop :=
  P.endpointOddCount < 3 * P.terminalGap

/--
`SingleLiftGapCondition` は path の細部には依存せず、endpoint odd count `p` の
critical 2--3 gap だけの命題に書き直せる。
-/
theorem singleLiftGapCondition_iff_criticalGap
    (P : FirstPassagePath) :
    P.SingleLiftGapCondition ↔
      P.endpointOddCount <
        3 * (2 ^ Critical.criticalTwoDepth P.endpointOddCount -
          3 ^ P.endpointOddCount) := by
  unfold SingleLiftGapCondition
  rw [P.terminalGap_eq_criticalGap]

/--
`p < 3D` のもとでは、capacity 内の start は parity modulus `2^H` より小さい。
-/
theorem start_lt_parityModulus_of_withinCapacity
    {P : FirstPassagePath}
    {x : ℕ}
    (hGap : P.SingleLiftGapCondition)
    (hcap : P.WithinCapacity x) :
    x < parityModulus P.word := by
  unfold SingleLiftGapCondition at hGap
  have hB := P.affineConst_le_endpointOddCount_mul_threePow_pred
  by_cases hp0 : P.endpointOddCount = 0
  · have hB0 : affineConst P.word = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hp0] using hB
    have hx0 : x = 0 := by
      unfold WithinCapacity at hcap
      rw [hB0] at hcap
      have hD := P.terminalGap_pos
      nlinarith
    subst x
    simp [parityModulus]
  · have hpPos : 0 < P.endpointOddCount := Nat.pos_of_ne_zero hp0
    have hpowPos : 0 < 3 ^ (P.endpointOddCount - 1) :=
      Nat.pow_pos (by decide)
    have hGapMul :
        P.endpointOddCount * 3 ^ (P.endpointOddCount - 1) <
          (3 * P.terminalGap) * 3 ^ (P.endpointOddCount - 1) :=
      (Nat.mul_lt_mul_right hpowPos).2 hGap
    have hpEq :
        P.endpointOddCount = (P.endpointOddCount - 1) + 1 := by
      omega
    have hScaleEq :
        (3 * P.terminalGap) * 3 ^ (P.endpointOddCount - 1) =
          P.terminalGap * 3 ^ P.endpointOddCount := by
      rw [hpEq, pow_succ]
      ring_nf
      simp
    rw [hScaleEq] at hGapMul
    have hBlt :
        affineConst P.word <
          P.terminalGap * 3 ^ P.endpointOddCount :=
      lt_of_le_of_lt hB hGapMul
    have hDxlt :
        P.terminalGap * x <
          P.terminalGap * 3 ^ P.endpointOddCount :=
      lt_of_le_of_lt hcap hBlt
    have hxThree : x < 3 ^ P.endpointOddCount :=
      (Nat.mul_lt_mul_left P.terminalGap_pos).1 hDxlt
    have hxTwo : x < 2 ^ P.length :=
      lt_trans hxThree P.terminal_contracting
    simpa [parityModulus, length] using hxTwo

/--
`p < 3D` のもとで、非下降 affine realization の start は
parity cylinder の最小代表そのものに一致する。

これが standard parity first-passage に対する single-lift reduction。
-/
theorem nondecreasing_start_eq_leastRepresentative
    {P : FirstPassagePath}
    {x y : ℕ}
    (hGap : P.SingleLiftGapCondition)
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    x = leastRepresentative P.word := by
  have hcap := P.withinCapacity_of_affine_start_le_end h hxy
  have hxlt := P.start_lt_parityModulus_of_withinCapacity hGap hcap
  have hmod := h.start_mod_eq_leastRepresentative
  have hxmod : x % parityModulus P.word = x := Nat.mod_eq_of_lt hxlt
  rw [hxmod] at hmod
  exact hmod

/-- exact parity trace についての single-lift reduction。 -/
theorem nondecreasing_trace_start_eq_leastRepresentative
    {P : FirstPassagePath}
    {x y : ℕ}
    (hGap : P.SingleLiftGapCondition)
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y) :
    x = leastRepresentative P.word :=
  P.nondecreasing_start_eq_leastRepresentative hGap h.affine hxy

/--
同じ first-passage parity word には、`p < 3D` のもとで
非下降する natural start は高々一つしかない。
-/
theorem nondecreasing_start_unique
    {P : FirstPassagePath}
    {x₁ y₁ x₂ y₂ : ℕ}
    (hGap : P.SingleLiftGapCondition)
    (h₁ : AffineRealizes P.word x₁ y₁)
    (h₂ : AffineRealizes P.word x₂ y₂)
    (h₁nd : x₁ ≤ y₁)
    (h₂nd : x₂ ≤ y₂) :
    x₁ = x₂ := by
  rw [P.nondecreasing_start_eq_leastRepresentative hGap h₁ h₁nd]
  rw [P.nondecreasing_start_eq_leastRepresentative hGap h₂ h₂nd]

end FirstPassagePath
end CSTMicro
end Collatz3
