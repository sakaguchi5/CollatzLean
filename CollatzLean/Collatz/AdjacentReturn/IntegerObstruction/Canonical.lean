import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Primitive
import CollatzLean.Collatz.AdjacentReturn.CanonicalLatePacket

/-!
# Baker/canonical refinement の純整数側インターフェース

Baker 型 gap 入力から得る canonical start/end と zero-cylinder を、
純整数 obstruction の追加 refinement として保持する。

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

end CanonicalLateArithmeticData

end IntegerObstruction
end AdjacentReturn
end Collatz
