import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Primitive
import CollatzLean.Collatz.AdjacentReturn.CanonicalLatePacket

/-!
# Baker/canonical refinement の純整数側インターフェース

Baker 型 gap 入力から得る canonical start/end と zero-cylinder を、
純整数 obstruction の追加 refinement として保持する。

canonical Late arithmetic から既存 `CanonicalLatePacket` への pure finite bridge も
この層に置く。

このファイルでは Baker 型入力そのものを structure に埋め込まず、
canonical 化済みであるという有限語条件だけを package 化する。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- 一つの first crossing が canonical representative そのものであること。 -/
structure CanonicalFirstCrossingArithmeticData
    {B : BlockArithmeticData}
    (F : FirstCrossingArithmeticData B) : Prop where
  start_eq :
    B.startValue = Word.canonicalStart F.word
  endpoint_eq :
    F.endpointValue = Word.canonicalEnd F.word

/--
Late block の canonical / zero-cylinder refinement。

`fullStart_eq` と `fullEnd_eq` は first crossing と suffix を連結した全 word も
同じ actual adjacent block の canonical representative であることを保持する。
-/
structure CanonicalLateArithmeticData
    {C : ContractingBlockArithmetic}
    (L : LateBlockArithmeticData C) : Prop where
  crossingCanonical :
    CanonicalFirstCrossingArithmeticData L.crossing
  fullStart_eq :
    C.base.startValue =
      Word.canonicalStart (L.crossing.word ++ L.suffix)
  fullEnd_eq :
    C.base.startValue + C.base.valueGap =
      Word.canonicalEnd (L.crossing.word ++ L.suffix)
  zeroDigit :
    Word.extensionDigit L.crossing.word L.suffix = 0
  allExtensionDigitsZero :
    Word.AllExtensionDigitsZero L.crossing.word L.suffix

/-- chain の index `n` における Late canonical 条件。 -/
def CanonicalLateAt
    (C : ContractingIntegerChain) (n : ℕ) : Prop :=
  ∀ L : LateBlockArithmeticData (C.block n),
    L.crossing = C.firstCrossing n →
      CanonicalLateArithmeticData L

/--
contracting integer chain の eventual canonical refinement。

first-crossing length が十分大きい tail だけに canonical 条件を要求するため、
`cutoff` を明示して core obstruction と分離する。
-/
structure CanonicalIntegerRefinement (C : ContractingIntegerChain) where
  cutoff : ℕ
  crossingCanonical :
    ∀ n : ℕ,
      cutoff ≤ n →
        CanonicalFirstCrossingArithmeticData (C.firstCrossing n)
  lateCanonical :
    ∀ n : ℕ,
      cutoff ≤ n →
        CanonicalLateAt C n

namespace CanonicalLateArithmeticData

/-- zero-cylinder は aggregate digit 0 を直接保持する。 -/
theorem extensionDigit_eq_zero
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    Word.extensionDigit L.crossing.word L.suffix = 0 :=
  K.zeroDigit

/-- canonical Late integer data は既存 finite `CanonicalLatePacket` を与える。 -/
theorem toCanonicalLatePacket
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    CanonicalLatePacket L.crossing.word L.suffix := by
  refine {
    valid := ?_
    crossing := L.crossing.crossing
    suffix_nonempty := L.suffix_nonempty
    suffix_allSuffixesContracting := L.suffix_allSuffixesContracting
    zeroDigit := K.zeroDigit
    source_lt_endpoint := ?_
    endpoint_lt_peak := ?_
  }
  · rw [← L.word_eq_crossing_append_suffix]
    exact C.base.word_valid
  · rw [← K.crossingCanonical.start_eq, ← K.fullEnd_eq]
    have hgap := C.base.valueGap_pos
    omega
  · rw [← K.fullEnd_eq, ← K.crossingCanonical.endpoint_eq]
    rw [L.crossing.endpoint_eq_start_add_gap]
    exact
      Nat.add_lt_add_left
        L.valueGap_lt_returnGap
        C.base.startValue

/-- bridge 後の packet source は integer block start と一致する。 -/
theorem packet_source_eq_startValue
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.source = C.base.startValue := by
  unfold CanonicalLatePacket.source
  exact K.crossingCanonical.start_eq.symm

/-- bridge 後の packet peak は first-crossing endpoint と一致する。 -/
theorem packet_peak_eq_crossingEndpoint
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.peak = L.crossing.endpointValue := by
  unfold CanonicalLatePacket.peak
  exact K.crossingCanonical.endpoint_eq.symm

/-- bridge 後の packet endpoint は adjacent endpoint と一致する。 -/
theorem packet_endpoint_eq_nextValue
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.endpoint = C.base.nextValue := by
  unfold CanonicalLatePacket.endpoint BlockArithmeticData.nextValue
  exact K.fullEnd_eq.symm

end CanonicalLateArithmeticData

end IntegerObstruction
end AdjacentReturn
end Collatz
