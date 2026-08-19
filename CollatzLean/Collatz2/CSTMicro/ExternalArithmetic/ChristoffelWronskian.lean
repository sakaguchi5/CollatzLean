import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalChristoffelPacket

/-!
# Raw Christoffel Wronskian

critical convergent `(p_j,q_j)` に対して

  φ_j = criticalChristoffelPhiAt D j
  Γ_j = 2^q_j - 3^p_j

と置く。

raw Wronskian

  W_j = φ_j Γ_(j+1) - φ_(j+1) Γ_j

は、前段の議論で現れた two-block determinant そのもの。
このファイルでは

* raw gap / raw Wronskian / affine defect を explicit に定義する。
* affine defect から common parameter が消える exact Wronskian identity を証明する。
* concatenation 型の positive linear update に対する determinant transport を証明する。
* consecutive critical blocks に期待する exact monomial law を pure certificate として隔離する。

最後の certificate 自体には axiom / sorry を置かない。
後段はこの pure law だけに依存し、actual Farey/Christoffel recursion からの構成は
独立した次の数学的課題として残す。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- critical convergent の signed raw power gap `2^q - 3^p`。 -/
def criticalRawPowerGap
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  (2 : ℤ) ^ D.q j - (3 : ℤ) ^ D.p j

/-- consecutive critical Christoffel blocks の raw Wronskian。 -/
def criticalRawChristoffelWronskianNext
    (D : CriticalContinuedFractionData)
    (j : ℕ) : ℤ :=
  criticalChristoffelPhiAt D j * criticalRawPowerGap D (j + 1) -
    criticalChristoffelPhiAt D (j + 1) * criticalRawPowerGap D j

/-- block `j` の affine defect `φ_j - Γ_j*y`。 -/
def criticalRawChristoffelDefect
    (D : CriticalContinuedFractionData)
    (j : ℕ)
    (y : ℤ) : ℤ :=
  criticalChristoffelPhiAt D j - criticalRawPowerGap D j * y

/--
二つの affine defect の cross combination では common parameter `y` が exact に消え、
raw Wronskian だけが残る。
-/
theorem criticalRawChristoffelDefect_cross_eq_wronskian
    (D : CriticalContinuedFractionData)
    (j : ℕ)
    (y : ℤ) :
    criticalRawPowerGap D (j + 1) *
          criticalRawChristoffelDefect D j y -
        criticalRawPowerGap D j *
          criticalRawChristoffelDefect D (j + 1) y =
      criticalRawChristoffelWronskianNext D j := by
  unfold criticalRawChristoffelDefect
    criticalRawChristoffelWronskianNext
  ring

/-! ## generic two-block determinant transport -/

/--
`W = a*U + b*V` という同じ linear update を numerator / gap の両方に施すと、
left-vs-new determinant は `b` 倍になる。
-/
theorem rawWronskian_right_linear_transport
    {AU AV AW GU GV GW a b : ℤ}
    (hA : AW = a * AU + b * AV)
    (hG : GW = a * GU + b * GV) :
    AU * GW - AW * GU =
      b * (AU * GV - AV * GU) := by
  rw [hA, hG]
  ring

/--
同じ linear update に対し、new-vs-right determinant は `a` 倍になる。
-/
theorem rawWronskian_left_linear_transport
    {AU AV AW GU GV GW a b : ℤ}
    (hA : AW = a * AU + b * AV)
    (hG : GW = a * GU + b * GV) :
    AW * GV - AV * GW =
      a * (AU * GV - AV * GU) := by
  rw [hA, hG]
  ring

/--
Christoffel/Farey concatenationで期待する specialization。

numerator と gap がとも

  new = 3^p * left + 2^q * right

で更新されるなら、left-vs-new Wronskian は `2^q` 倍。
-/
theorem rawWronskian_christoffel_right_transport
    {AU AV AW GU GV GW : ℤ}
    {p q : ℕ}
    (hA :
      AW = (3 : ℤ) ^ p * AU + (2 : ℤ) ^ q * AV)
    (hG :
      GW = (3 : ℤ) ^ p * GU + (2 : ℤ) ^ q * GV) :
    AU * GW - AW * GU =
      (2 : ℤ) ^ q * (AU * GV - AV * GU) := by
  exact rawWronskian_right_linear_transport hA hG

/--
同じ Christoffel/Farey concatenationで new-vs-right Wronskian は `3^p` 倍。
-/
theorem rawWronskian_christoffel_left_transport
    {AU AV AW GU GV GW : ℤ}
    {p q : ℕ}
    (hA :
      AW = (3 : ℤ) ^ p * AU + (2 : ℤ) ^ q * AV)
    (hG :
      GW = (3 : ℤ) ^ p * GU + (2 : ℤ) ^ q * GV) :
    AW * GV - AV * GW =
      (3 : ℤ) ^ p * (AU * GV - AV * GU) := by
  exact rawWronskian_left_linear_transport hA hG

/-! ## exact raw critical law -/

/--
consecutive critical Christoffel blocks に対する exact raw Wronskian law。

* even `j` は below -> above:

    W_j = - 2^(q_j-1) 3^(p_(j+1)-1)

* odd `j` は above -> below:

    W_j = + 2^(q_(j+1)-1) 3^(p_j-1)

この structure は pure arithmetic certificate であり、axiom ではない。
actual power-Farey recursion からこの object を構成することが次の独立課題になる。
-/
structure CriticalRawChristoffelWronskianLaw
    (D : CriticalContinuedFractionData) : Prop where
  even_next :
    ∀ j : ℕ,
      D.start ≤ j →
      j % 2 = 0 →
      criticalRawChristoffelWronskianNext D j =
        -((2 : ℤ) ^ (D.q j - 1) *
          (3 : ℤ) ^ (D.p (j + 1) - 1))

  odd_next :
    ∀ j : ℕ,
      D.start ≤ j →
      j % 2 = 1 →
      criticalRawChristoffelWronskianNext D j =
        (2 : ℤ) ^ (D.q (j + 1) - 1) *
          (3 : ℤ) ^ (D.p j - 1)

namespace CriticalRawChristoffelWronskianLaw

/-- even branch raw Wronskian は strict negative。 -/
theorem even_next_neg
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjEven : j % 2 = 0) :
    criticalRawChristoffelWronskianNext D j < 0 := by
  rw [W.even_next j hjStart hjEven]
  have hpos :
      0 <
        (2 : ℤ) ^ (D.q j - 1) *
          (3 : ℤ) ^ (D.p (j + 1) - 1) := by
    positivity
  omega

/-- odd branch raw Wronskian は strict positive。 -/
theorem odd_next_pos
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjOdd : j % 2 = 1) :
    0 < criticalRawChristoffelWronskianNext D j := by
  rw [W.odd_next j hjStart hjOdd]
  positivity

/-- exact raw law があれば consecutive Wronskian は全 relevant index で nonzero。 -/
theorem next_ne_zero
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j) :
    criticalRawChristoffelWronskianNext D j ≠ 0 := by
  have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · exact ne_of_gt (W.odd_next_pos hjStart hjOdd)
  · have hjEven : j % 2 = 0 := by omega
    exact ne_of_lt (W.even_next_neg hjStart hjEven)

end CriticalRawChristoffelWronskianLaw

end ExternalArithmetic
end CSTMicro
end Collatz2
