import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Contracting

/-!
# Late first-crossing の純整数 refinement

contracting adjacent block の first crossing が block 終端より手前で終わる場合に、
残り suffix と first-crossing peak / adjacent endpoint の差を純整数データとして保持する。

この層では Baker 型 gap 下界や計算検証境界を仮定しない。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/--
contracting block の Late first crossing に付随する追加純算術データ。

`crossing` が peak まで、`suffix` が peak から adjacent endpoint までを表す。
-/
structure LateBlockArithmeticData (C : ContractingBlockArithmetic) where
  crossing : FirstCrossingArithmeticData C.base
  late : crossing.length < C.base.length
  valueGap_lt_returnGap : C.base.valueGap < crossing.returnGap
  suffix : Collatz.Word
  word_eq_crossing_append_suffix :
    C.base.word = crossing.word ++ suffix
  suffix_nonempty : suffix ≠ []
  suffix_allSuffixesContracting : suffix.AllSuffixesContracting
  suffix_length :
    suffix.length = C.base.length - crossing.length
  totalExponent_split :
    C.base.totalExponent = crossing.totalExponent + suffix.twoSteps
  suffixScaledEquation :
    2 ^ suffix.twoSteps * (C.base.startValue + C.base.valueGap) =
      3 ^ suffix.length * crossing.endpointValue + suffix.affineConst

namespace LateBlockArithmeticData

/-- first-crossing peak から adjacent endpoint までの正の落差。 -/
def peakDrop
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) : ℕ :=
  L.crossing.returnGap - C.base.valueGap

/-- Late suffix の multiplicative contracting gap。 -/
def suffixGap
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) : ℕ :=
  2 ^ L.suffix.twoSteps - 3 ^ L.suffix.length

/--
Late geometry から自然に現れる正の commutator core。

`h = suffixGap`, `g = crossing.multiplicativeGap`,
`d = crossing.returnGap`, `r = peakDrop` とすると
`3^p*h*d + 2^K*g*r`。
-/
def commutatorCore
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) : ℕ :=
  3 ^ L.crossing.length * L.suffixGap * L.crossing.returnGap +
    2 ^ L.suffix.twoSteps * L.crossing.multiplicativeGap * L.peakDrop

/-- peak drop は正。 -/
theorem peakDrop_pos
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    0 < L.peakDrop := by
  unfold peakDrop
  exact Nat.sub_pos_of_lt L.valueGap_lt_returnGap

/-- adjacent gap と peak drop の和は first-crossing return gap。 -/
theorem valueGap_add_peakDrop
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    C.base.valueGap + L.peakDrop = L.crossing.returnGap := by
  unfold peakDrop
  exact Nat.add_sub_of_le (Nat.le_of_lt L.valueGap_lt_returnGap)

/-- Late suffix 全体は contracting。 -/
theorem suffix_contracting
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    L.suffix.Contracting :=
  L.suffix_allSuffixesContracting.whole L.suffix_nonempty

/-- Late suffix gap は正。 -/
theorem suffixGap_pos
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    0 < L.suffixGap := by
  unfold suffixGap
  have h := L.suffix_contracting
  unfold Word.Contracting at h
  simpa [Word.oddSteps] using Nat.sub_pos_of_lt h

/--
Late suffix の exact descent equation。

`h * peak = 2^K * peakDrop + affine(C)`。
-/
theorem suffixGap_peak_eq
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    L.suffixGap * L.crossing.endpointValue =
      2 ^ L.suffix.twoSteps * L.peakDrop + L.suffix.affineConst := by
  have hpeak :
      L.crossing.endpointValue =
        (C.base.startValue + C.base.valueGap) + L.peakDrop := by
    rw [L.crossing.endpoint_eq_start_add_gap, ← L.valueGap_add_peakDrop]
    omega
  have hscaled := L.suffixScaledEquation
  have hcontract :
      3 ^ L.suffix.length < 2 ^ L.suffix.twoSteps := by
    have h := L.suffix_contracting
    unfold Word.Contracting at h
    simpa [Word.oddSteps] using h
  have htwo :
      2 ^ L.suffix.twoSteps =
        3 ^ L.suffix.length + L.suffixGap := by
    unfold suffixGap
    exact (Nat.add_sub_of_le hcontract.le).symm
  have hcancel :
      3 ^ L.suffix.length * L.crossing.endpointValue +
          L.suffixGap * L.crossing.endpointValue =
        3 ^ L.suffix.length * L.crossing.endpointValue +
          (2 ^ L.suffix.twoSteps * L.peakDrop + L.suffix.affineConst) := by
    calc
      3 ^ L.suffix.length * L.crossing.endpointValue +
            L.suffixGap * L.crossing.endpointValue
          = 2 ^ L.suffix.twoSteps * L.crossing.endpointValue := by
              rw [htwo]
              ring
      _ =
          2 ^ L.suffix.twoSteps *
            ((C.base.startValue + C.base.valueGap) + L.peakDrop) := by
              rw [hpeak]
      _ =
          2 ^ L.suffix.twoSteps * (C.base.startValue + C.base.valueGap) +
            2 ^ L.suffix.twoSteps * L.peakDrop := by ring
      _ =
          (3 ^ L.suffix.length * L.crossing.endpointValue +
            L.suffix.affineConst) +
            2 ^ L.suffix.twoSteps * L.peakDrop := by
              rw [hscaled]
      _ =
          3 ^ L.suffix.length * L.crossing.endpointValue +
            (2 ^ L.suffix.twoSteps * L.peakDrop + L.suffix.affineConst) := by
              ring
  exact Nat.add_left_cancel hcancel

/--
first crossing と Late suffix の affine data を消去した exact commutator identity。
-/
theorem commutator_balance
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    L.suffixGap * L.crossing.affine =
      L.crossing.multiplicativeGap * L.suffix.affineConst +
        L.commutatorCore := by
  have hA := L.crossing.returnIdentity
  have hC := L.suffixGap_peak_eq
  unfold commutatorCore
  rw [hA]
  calc
    L.suffixGap *
        (3 ^ L.crossing.length * L.crossing.returnGap +
          L.crossing.multiplicativeGap * L.crossing.endpointValue)
        =
      3 ^ L.crossing.length * L.suffixGap * L.crossing.returnGap +
        L.crossing.multiplicativeGap *
          (L.suffixGap * L.crossing.endpointValue) := by ring
    _ =
      3 ^ L.crossing.length * L.suffixGap * L.crossing.returnGap +
        L.crossing.multiplicativeGap *
          (2 ^ L.suffix.twoSteps * L.peakDrop + L.suffix.affineConst) := by
            rw [hC]
    _ =
      L.crossing.multiplicativeGap * L.suffix.affineConst +
        (3 ^ L.crossing.length * L.suffixGap * L.crossing.returnGap +
          2 ^ L.suffix.twoSteps * L.crossing.multiplicativeGap * L.peakDrop) := by
            ring

/-- commutator core は正。 -/
theorem commutatorCore_pos
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    0 < L.commutatorCore := by
  unfold commutatorCore
  have hh := L.suffixGap_pos
  have hd := L.crossing.returnGap_pos
  have hp : 0 < 3 ^ L.crossing.length := Nat.pow_pos (by omega)
  have hfirst :
      0 < 3 ^ L.crossing.length * L.suffixGap * L.crossing.returnGap := by
    exact Nat.mul_pos (Nat.mul_pos hp hh) hd
  omega

end LateBlockArithmeticData
end IntegerObstruction
end AdjacentReturn
end Collatz
