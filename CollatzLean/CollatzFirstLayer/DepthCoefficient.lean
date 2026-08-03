import CollatzLean.CollatzFirstLayer.FirstCarry

/-!
# return深さと奇数係数の更新

terminal transitionで現れる

`2^(L+«λ»')u' = 2^«λ»(3^P u+w)`

を、carry深さ `t` によって分解する。
深さ保存則と係数更新則は仮定として置かず、完全2進分解の一意性から導く。
-/

namespace CollatzFirstLayer

/-- 深さ・係数更新に必要な有限整数データ。 -/
structure DepthCoefficientData where
  L : ℕ
  P : ℕ
  «λ» : ℕ
  «λnext» : ℕ
  t : ℕ
  u : ℕ
  unext : ℕ
  w : ℕ
  carryOddPart : ℕ
  transition :
    2 ^ (L + «λnext») * unext =
      2 ^ «λ» * (3 ^ P * u + w)
  carryFactorization :
    3 ^ P * u + w = 2 ^ t * carryOddPart
  unextOdd : Odd unext
  carryOdd : Odd carryOddPart

namespace DepthCoefficientData

/-- transitionの両辺を完全2進分解として比較する。 -/
lemma exact_factor_comparison (d : DepthCoefficientData) :
    d.L + d.«λnext» = d.«λ» + d.t ∧
      d.unext = d.carryOddPart := by
  have hleft :
      ExactTwoFactor
        (2 ^ (d.L + d.«λnext») * d.unext)
        (d.L + d.«λnext») d.unext :=
    ⟨rfl, d.unextOdd⟩
  have hright :
      ExactTwoFactor
        (2 ^ (d.L + d.«λnext») * d.unext)
        (d.«λ» + d.t) d.carryOddPart := by
    refine ⟨?_, d.carryOdd⟩
    calc
      2 ^ (d.L + d.«λnext») * d.unext
          = 2 ^ d.«λ» * (3 ^ d.P * d.u + d.w) := d.transition
      _ = 2 ^ d.«λ» * (2 ^ d.t * d.carryOddPart) := by
            rw [d.carryFactorization]
      _ = 2 ^ (d.«λ» + d.t) * d.carryOddPart := by
            rw [pow_add]
            ring
  exact exactTwoFactor_unique hleft hright

/-- return深さの更新は `«λ»+t=L+«λ»'` で完全に表される。 -/
theorem depth_update (d : DepthCoefficientData) :
    d.«λ» + d.t = d.L + d.«λnext» :=
  d.exact_factor_comparison.1.symm

/-- carry分解後の奇数部分は次のreturn係数に一致する。 -/
theorem coefficient_update (d : DepthCoefficientData) :
    d.unext = d.carryOddPart :=
  d.exact_factor_comparison.2

/-- 深さが増えるならcarry深さは消費長より大きい。 -/
lemma carry_exceeds_length_of_depth_increase (d : DepthCoefficientData)
    (h : d.«λ» < d.«λnext») : d.L < d.t := by
  have hb := d.depth_update
  omega

/-- 深さが保たれるならcarry深さと消費長は等しい。 -/
lemma carry_eq_length_of_depth_eq (d : DepthCoefficientData)
    (h : d.«λnext» = d.«λ») : d.t = d.L := by
  have hb := d.depth_update
  omega

/-- 深さが減るなら消費長がcarry深さを上回る。 -/
lemma carry_lt_length_of_depth_decrease (d : DepthCoefficientData)
    (h : d.«λnext» < d.«λ») : d.t < d.L := by
  have hb := d.depth_update
  omega

end DepthCoefficientData

end CollatzFirstLayer
