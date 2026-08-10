import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.ExactLate

/-!
# Late suffix の追加幾何

`LateBlockArithmeticData` から無条件に得られる粗い強化と、
actual future-minimum 性を有限データへ移す endpoint floor をまとめる。

このファイルの `LateSuffixEndpointFloorData` は純有限データであり、
`ofActualFirstCrossing` の境界を越えた後は `OddOrbit` を保持しない。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

namespace LateBlockArithmeticData

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

namespace LateSuffixEndpointFloorData

/--
actual Late first crossing から suffix の future-minimum floor を純有限データへ移す。
この constructor の外では `OddOrbit` を保持しない。
-/
theorem ofActualFirstCrossing
    {O : OddOrbit} {R : State O}
    (hC : R.IsContracting)
    (F : FirstCrossingData R)
    (hLate : F.IsLate) :
    LateSuffixEndpointFloorData
      (LateBlockArithmeticData.ofActualFirstCrossing hC F hLate) := by
  let L : LateBlockArithmeticData
      (ContractingBlockArithmetic.ofState R hC) :=
    LateBlockArithmeticData.ofActualFirstCrossing hC F hLate
  change LateSuffixEndpointFloorData L
  refine {
    peak_odd := ?_
    prefixFloor := ?_
  }
  · change Odd F.endpointValue
    unfold FirstCrossingData.endpointValue
    exact O.value_odd _
  · intro k hkPos hkLe
    let S : Collatz.Word :=
      O.segment
        (R.startIndex + F.length)
        (R.length - F.length)
    have hSuffix : L.suffix = S := by
      rfl
    have hkLeS : k ≤ S.length := by
      simpa [hSuffix] using hkLe
    have hkLeQ : k ≤ R.length - F.length := by
      simpa [S] using hkLeS
    have htake :
        S.take k =
          O.segment (R.startIndex + F.length) k := by
      exact O.segment_take_of_le hkLeQ
    let y : ℕ :=
      O.value (R.startIndex + F.length + k)
    refine ⟨y, ?_, ?_⟩
    · rw [hSuffix, htake]
      change
        Word.Runs
          (O.segment (R.startIndex + F.length) k)
          F.endpointValue
          y
      simpa [y, FirstCrossingData.endpointValue, Nat.add_assoc] using
        O.runsSegment (R.startIndex + F.length) k
    · change R.startValue + R.valueGap ≤ y
      rw [← R.nextValue_eq_startValue_add_valueGap]
      have hfloor :=
        R.nextValue_le_positiveEndpoint
          (F.length + k) (by omega)
      simpa [y, Nat.add_assoc] using hfloor

end LateSuffixEndpointFloorData

end IntegerObstruction
end AdjacentReturn
end Collatz
