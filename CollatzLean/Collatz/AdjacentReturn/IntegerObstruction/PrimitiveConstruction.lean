import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Primitive

/-!
# primitive Late data の機械的 2-adic construction

`PrimitiveLateCommutatorData` が与えられた後の正 quotient と
primitive commutator の exact 2-adic factorization は外部 provider なしで選べる。

large-index / equal-cancellation の outcome 自体はこのファイルでは仮定しない。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

namespace PrimitiveLateCommutatorData

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

end IntegerObstruction
end AdjacentReturn
end Collatz
