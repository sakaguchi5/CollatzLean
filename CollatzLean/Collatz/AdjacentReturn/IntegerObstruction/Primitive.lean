import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Late

/-!
# Late commutator の primitive / 2-adic refinement

Late first-crossing から得た commutator を center gcd で primitive 化し、
二項の 2-adic depth が異なる枝と equal-cancellation 枝を分離する。

primitive data が得られた後の正 quotient と exact 2-adic depth の選択は
このファイル内で機械的に構成する。

このファイルは追加制約の純整数 package を定義する。
外部計算境界や Baker 型 gap 下界は仮定しない。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- Late commutator の center-gcd primitive 化。 -/
structure PrimitiveLateCommutatorData
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) where
  prefixCenterGcd : ℕ
  suffixCenterGcd : ℕ
  prefixAffinePrimitive : ℕ
  prefixGapPrimitive : ℕ
  suffixAffinePrimitive : ℕ
  suffixGapPrimitive : ℕ
  prefixReturnQuotient : ℕ
  suffixDropQuotient : ℕ

  prefixCenterGcd_eq :
    prefixCenterGcd =
      Nat.gcd L.crossing.affine L.crossing.multiplicativeGap
  suffixCenterGcd_eq :
    suffixCenterGcd =
      Nat.gcd L.suffix.affineConst L.suffixGap

  prefixAffine_eq :
    L.crossing.affine = prefixCenterGcd * prefixAffinePrimitive
  prefixGap_eq :
    L.crossing.multiplicativeGap = prefixCenterGcd * prefixGapPrimitive
  suffixAffine_eq :
    L.suffix.affineConst = suffixCenterGcd * suffixAffinePrimitive
  suffixGap_eq :
    L.suffixGap = suffixCenterGcd * suffixGapPrimitive

  returnGap_eq :
    L.crossing.returnGap = prefixCenterGcd * prefixReturnQuotient
  peakDrop_eq :
    L.peakDrop = suffixCenterGcd * suffixDropQuotient

  prefix_coprime :
    Nat.Coprime prefixAffinePrimitive prefixGapPrimitive
  suffix_coprime :
    Nat.Coprime suffixAffinePrimitive suffixGapPrimitive

namespace PrimitiveLateCommutatorData

/-- primitive commutator の正の整数表示。 -/
def primitiveCommutator
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) : ℕ :=
  3 ^ L.crossing.length * P.suffixGapPrimitive * P.prefixReturnQuotient +
    2 ^ L.suffix.twoSteps * P.prefixGapPrimitive * P.suffixDropQuotient

/-- primitive center determinant。 -/
def centerDeterminant
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) : ℤ :=
  (P.suffixGapPrimitive : ℤ) * P.prefixAffinePrimitive -
    (P.prefixGapPrimitive : ℤ) * P.suffixAffinePrimitive

/-- primitive commutator は正。 -/
theorem primitiveCommutator_pos
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    0 < P.primitiveCommutator := by
  have hd : 0 < P.prefixReturnQuotient := by
    have hret := L.crossing.returnGap_pos
    rw [P.returnGap_eq] at hret
    by_contra hzero
    have hz : P.prefixReturnQuotient = 0 := by omega
    rw [hz] at hret
    simp at hret
  have hh : 0 < P.suffixGapPrimitive := by
    have hgap := L.suffixGap_pos
    rw [P.suffixGap_eq] at hgap
    by_contra hzero
    have hz : P.suffixGapPrimitive = 0 := by omega
    rw [hz] at hgap
    simp at hgap
  unfold primitiveCommutator
  have hp : 0 < 3 ^ L.crossing.length := Nat.pow_pos (by omega)
  have hfirst :
      0 < 3 ^ L.crossing.length * P.suffixGapPrimitive * P.prefixReturnQuotient := by
    exact Nat.mul_pos (Nat.mul_pos hp hh) hd
  omega

/-- primitive return quotient は正。 -/
theorem prefixReturnQuotient_pos
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    0 < P.prefixReturnQuotient := by
  have hret := L.crossing.returnGap_pos
  rw [P.returnGap_eq] at hret
  by_contra hnot
  have hz : P.prefixReturnQuotient = 0 := by
    omega
  rw [hz] at hret
  simp at hret

/-- primitive suffix-drop quotient は正。 -/
theorem suffixDropQuotient_pos
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    0 < P.suffixDropQuotient := by
  have hdrop := L.peakDrop_pos
  rw [P.peakDrop_eq] at hdrop
  by_contra hnot
  have hz : P.suffixDropQuotient = 0 := by
    omega
  rw [hz] at hdrop
  simp at hdrop

end PrimitiveLateCommutatorData

/-- primitive return/drop quotient の exact 2-adic depth。 -/
structure PrimitiveDepthData
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) where
  prefixDepth : ℕ
  prefixOddPart : ℕ
  suffixDepth : ℕ
  suffixOddPart : ℕ
  prefixFactor :
    TwoAdic.ExactFactor
      P.prefixReturnQuotient prefixDepth prefixOddPart
  suffixFactor :
    TwoAdic.ExactFactor
      P.suffixDropQuotient suffixDepth suffixOddPart

namespace PrimitiveLateCommutatorData

/-- primitive data の二つの正 quotient に exact 2-adic depth を選ぶ。 -/
noncomputable def toPrimitiveDepthData
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    PrimitiveDepthData P := by
  classical
  let hp :=
    TwoAdic.exists_of_pos
      P.prefixReturnQuotient
      P.prefixReturnQuotient_pos
  let t := Classical.choose hp
  let hp₁ := Classical.choose_spec hp
  let u := Classical.choose hp₁
  have htu :
      TwoAdic.ExactFactor
        P.prefixReturnQuotient t u :=
    Classical.choose_spec hp₁
  let hs :=
    TwoAdic.exists_of_pos
      P.suffixDropQuotient
      P.suffixDropQuotient_pos
  let w := Classical.choose hs
  let hs₁ := Classical.choose_spec hs
  let v := Classical.choose hs₁
  have hwv :
      TwoAdic.ExactFactor
        P.suffixDropQuotient w v :=
    Classical.choose_spec hs₁
  exact {
    prefixDepth := t
    prefixOddPart := u
    suffixDepth := w
    suffixOddPart := v
    prefixFactor := htu
    suffixFactor := hwv
  }

/-- primitive data があれば depth data の存在は自動。 -/
theorem exists_primitiveDepthData
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    Nonempty (PrimitiveDepthData P) :=
  ⟨P.toPrimitiveDepthData⟩

/-- primitive commutator 自体にも exact 2-adic factorization を選べる。 -/
theorem exists_primitiveCommutatorFactor
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (P : PrimitiveLateCommutatorData L) :
    ∃ d u : ℕ,
      TwoAdic.ExactFactor P.primitiveCommutator d u := by
  exact TwoAdic.exists_of_pos P.primitiveCommutator P.primitiveCommutator_pos

end PrimitiveLateCommutatorData

/--
primitive commutator の 2-adic depth 分岐。

unequal 枝では primitive odd index が `3^p` 以上。
equal 枝では suffix twoSteps と gap depth を合わせた logarithmic localization を保持する。
-/
inductive PrimitiveDepthOutcome
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    {P : PrimitiveLateCommutatorData L}
    (V : PrimitiveDepthData P) : Type
  | unequal
      (depth_ne :
        V.prefixDepth ≠ L.suffix.twoSteps + V.suffixDepth)
      (commutatorDepth : ℕ)
      (primitiveOddIndex : ℕ)
      (commutatorFactor :
        TwoAdic.ExactFactor
          P.primitiveCommutator
          commutatorDepth
          primitiveOddIndex)
      (largeIndex :
        3 ^ L.crossing.length ≤ primitiveOddIndex)
  | equalCancellation
      (depth_eq :
        V.prefixDepth = L.suffix.twoSteps + V.suffixDepth)
      (gapDepth : ℕ)
      (gapOddPart : ℕ)
      (gapFactor :
        TwoAdic.ExactFactor C.base.valueGap gapDepth gapOddPart)
      (suffixDepth_eq_gapDepth :
        V.suffixDepth = gapDepth)
      (localized :
        3 * 2 ^ (L.suffix.twoSteps + gapDepth) <
          L.crossing.length)

/-- Late block に対する primitive refinement 全体。 -/
structure PrimitiveLateConstraintData
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) where
  primitive : PrimitiveLateCommutatorData L
  depth : PrimitiveDepthData primitive
  outcome : PrimitiveDepthOutcome depth

end IntegerObstruction
end AdjacentReturn
end Collatz
