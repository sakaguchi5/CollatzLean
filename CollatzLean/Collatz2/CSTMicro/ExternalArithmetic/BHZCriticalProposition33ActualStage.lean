import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33Actual

/-!
# BHZ Proposition 3.3 actual stage

この stage で source chain は

  integer phase s
    -> unique BHZ/Ostrowski digits c_k
    -> actual shifted critical Beatty word
    -> published BHZ Proposition 3.3 exact cyclic prefix powers
    -> actualBHZCriticalProposition33WordFormula
    -> actualBHZCriticalProposition33
    -> CriticalBeattySquareAt

まで閉じる。

外部依存は `BHZPublishedProposition33Canonical` に明示した published
Proposition 3.3 の二 theorem だけ。
旧 `BHZCriticalInitialSquareBand` の absolute constant は使わない。

次段では standard / semistandard の exact root

  q_k,
  q_k - c_k q_(k-1)

を保持したまま Rhin growth と合成する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- Canonical packet specialization for downstream selector construction. -/
noncomputable def actualBHZCriticalCanonicalPacket
    (s : ℕ) : CriticalBHZPhasePacket s :=
  CriticalBHZPhasePacket.canonical s

end ExternalArithmetic
end CSTMicro
end Collatz2
