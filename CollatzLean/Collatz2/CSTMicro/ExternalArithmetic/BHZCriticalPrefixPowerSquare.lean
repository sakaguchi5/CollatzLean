import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33Port

/-!
# Realize BHZ arithmetic prefix-power candidates as actual Beatty squares

`BHZCriticalPrefixPowerCandidate` はこれまで

* level `k`,
* standard / semistandard kind,
* exact primitive-root length

だけを持つ arithmetic candidate だった。

BHZ Proposition 3.3 port と square eligibility を加えることで、
candidate に actual

  CriticalBeattySquareAt s root

を載せる。

この層でも partial quotients / Ostrowski digits はそのまま保持され、
uniform band constant は導入しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
actual `CriticalBeattySquareAt` まで実現された BHZ candidate。
-/
structure BHZCriticalRealizedSquareCandidate
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) where
  arithmetic : BHZCriticalPrefixPowerCandidate P
  square :
    CriticalBeattySquareAt s arithmetic.root

namespace BHZCriticalPrefixPowerCandidate

/--
standard arithmetic candidate を actual square candidate へ実現する。
-/
def realizeStandard
    (B : BHZCriticalProposition33)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k)
    (hSquare : BHZStandardSquareEligible P k) :
    BHZCriticalRealizedSquareCandidate P := {
  arithmetic := .standard P k
  square := by
    simpa [
      BHZCriticalPrefixPowerCandidate.standard
    ] using
      B.standard_squareAt P hk hSquare
}

/--
semistandard arithmetic candidate を actual square candidate へ実現する。
-/
def realizeSemistandard
    (B : BHZCriticalProposition33)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ)
    (hk : 1 ≤ k)
    (hSquare : BHZSemistandardSquareEligible P k) :
    BHZCriticalRealizedSquareCandidate P := {
  arithmetic := .semistandard P k
  square := by
    simpa [
      BHZCriticalPrefixPowerCandidate.semistandard
    ] using
      B.semistandard_squareAt P hk hSquare
}

end BHZCriticalPrefixPowerCandidate

namespace BHZCriticalRealizedSquareCandidate

/-- realized candidate の root は positive。 -/
theorem root_pos
    {s : ℕ}
    {P : CriticalBHZPhasePacket s}
    (C : BHZCriticalRealizedSquareCandidate P) :
    0 < C.arithmetic.root :=
  C.square.root_pos

/-- realized candidate の actual square theorem を直接取り出す。 -/
theorem squareAt
    {s : ℕ}
    {P : CriticalBHZPhasePacket s}
    (C : BHZCriticalRealizedSquareCandidate P) :
    CriticalBeattySquareAt s C.arithmetic.root :=
  C.square

end BHZCriticalRealizedSquareCandidate

end ExternalArithmetic
end CSTMicro
end Collatz2
