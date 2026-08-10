import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Contracting

/-!
# Late first-crossing の純整数 refinement

contracting adjacent block の first crossing が block 終端より手前で終わる場合に、
残り suffix と first-crossing peak / adjacent endpoint の差を純整数データとして保持する。

actual future-minimum 性から得る endpoint floor も純有限データとして定義し、
actual constructor の境界を越えた後は OddOrbit を保持しない。

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

/-- Late では adjacent gap 4 と正の peak drop から return gap は少なくとも5。 -/
theorem five_le_returnGap
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    5 ≤ L.crossing.returnGap := by
  have hgap : 4 ≤ C.base.valueGap :=
    C.base.four_le_valueGap
  have hdrop : 0 < L.peakDrop :=
    L.peakDrop_pos
  rw [← L.valueGap_add_peakDrop]
  omega

/-- Late では first-crossing length は少なくとも16。 -/
theorem sixteen_le_crossingLength
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) :
    16 ≤ L.crossing.length := by
  have hret := L.five_le_returnGap
  have hsharp := L.crossing.three_mul_returnGap_lt_length
  omega

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

/--
Late suffix の各 positive prefix endpoint が adjacent endpoint 以上に残ること。

`peak_odd` も actual constructor の境界で保存する。これにより
peak drop の parity を pure finite data 側だけで利用できる。
-/
structure LateSuffixEndpointFloorData
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) : Prop where
  peak_odd : Odd L.crossing.endpointValue
  prefixFloor :
    ∀ k : ℕ,
      0 < k →
      k ≤ L.suffix.length →
        ∃ y : ℕ,
          Word.Runs
            (L.suffix.take k)
            L.crossing.endpointValue
            y ∧
          C.base.nextValue ≤ y

namespace LateSuffixEndpointFloorData

/-- floor data があれば suffix の各 positive prefix endpoint を明示的に取れる。 -/
theorem exists_prefix_endpoint
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (D : LateSuffixEndpointFloorData L)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLe : k ≤ L.suffix.length) :
    ∃ y : ℕ,
      Word.Runs
        (L.suffix.take k)
        L.crossing.endpointValue
        y ∧
      C.base.nextValue ≤ y :=
  D.prefixFloor k hkPos hkLe

/-- peak と adjacent endpoint はとも奇数なので peak drop は偶数。 -/
theorem peakDrop_even
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (D : LateSuffixEndpointFloorData L) :
    Even L.peakDrop := by
  have hpeak :
      L.crossing.endpointValue =
        C.base.nextValue + L.peakDrop := by
    unfold BlockArithmeticData.nextValue
    rw [L.crossing.endpoint_eq_start_add_gap]
    rw [← L.valueGap_add_peakDrop]
    ring
  have hnextLePeak :
      C.base.nextValue ≤ L.crossing.endpointValue := by
    omega
  rcases D.peak_odd with ⟨a, ha⟩
  rcases C.base.next_odd with ⟨b, hb⟩
  have hb' :
      C.base.nextValue = 2 * b + 1 := by
    change
      C.base.startValue + C.base.valueGap =
        2 * b + 1
    exact hb
  have hba : b ≤ a := by
    rw [hb', ha] at hnextLePeak
    omega
  have hdrop :
      L.peakDrop = 2 * (a - b) := by
    rw [ha, hb'] at hpeak
    omega
  refine ⟨a - b, ?_⟩
  omega

/-- 正の偶数である peak drop は少なくとも2。 -/
theorem two_le_peakDrop
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (D : LateSuffixEndpointFloorData L) :
    2 ≤ L.peakDrop := by
  have hpos := L.peakDrop_pos
  rcases D.peakDrop_even with ⟨q, hq⟩
  omega

/-- actual floor を保持した Late data では return gap は少なくとも6。 -/
theorem six_le_returnGap
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (D : LateSuffixEndpointFloorData L) :
    6 ≤ L.crossing.returnGap := by
  have hgap : 4 ≤ C.base.valueGap :=
    C.base.four_le_valueGap
  have hdrop : 2 ≤ L.peakDrop :=
    D.two_le_peakDrop
  rw [← L.valueGap_add_peakDrop]
  omega

/-- actual floor を保持した Late data では first-crossing length は少なくとも19。 -/
theorem nineteen_le_crossingLength
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (D : LateSuffixEndpointFloorData L) :
    19 ≤ L.crossing.length := by
  have hret := D.six_le_returnGap
  have hsharp := L.crossing.three_mul_returnGap_lt_length
  omega

end LateSuffixEndpointFloorData

end IntegerObstruction
end AdjacentReturn
end Collatz
