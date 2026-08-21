import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPhaseDigitUniqueness

/-!
# Published BHZ Proposition 3.3 — exact canonical source boundary

Berthé--Holton--Zamboni, "Initial powers of Sturmian sequences",
Proposition 3.3 gives the exact initial powers of a Sturmian sequence in terms
of its S-adic/Ostrowski digits.

For the critical slope `α = log₂ 3 - 1` and the natural integer orbit
`T^s w`, the preceding files have already identified

* `criticalBHZa k` with BHZ `a_k`,
* `criticalBHZq k` with BHZ `q_k`,
* `(CriticalBHZPhasePacket.canonical s).digit k` with BHZ `c_k`,
* `criticalShiftBit s` with the actual shifted critical Beatty increment word,
* `bhzCriticalStandardWord` / `bhzCriticalSemistandardWord` with the literal
  finite τ-morphism roots occurring in Proposition 3.3.

従って外部文献から project が受け取るべき theorem boundary は、旧
`BHZCriticalInitialSquareBand` のような uniform constant ではなく、以下の
canonical cyclic-prefix statement そのもの。

重要:
このファイルの唯一の axiom は published Proposition 3.3 自体である。
`C_BHZ`、bounded partial quotients、Rhin estimate、Pure B statement は含まない。
将来 BHZ 論文全体（Lemma 2.4 / Proposition 2.7 の S-adic machinery）を Lean 内で
再証明する場合は、この axiom だけを置換すれば下流は変更不要。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
BHZ Proposition 3.3 specialized to the canonical integer-orbit coordinates of
the critical slope.

The standard length is exactly

  1_{a_(k+2)=c_(k+2)} q_k
    + Σ_{j=1}^{k+1} (a_j-c_j) q_(j-1),

encoded by `bhzCriticalStandardPowerNumerator`.
-/
axiom bhz2006_proposition33_standard_critical
    (s k : ℕ)
    (hk : 1 ≤ k) :
    BHZCriticalCyclicPrefixPower
      s
      (bhzCriticalStandardWord k)
      (bhzCriticalStandardPowerNumerator
        (CriticalBHZPhasePacket.canonical s) k)

/--
BHZ Proposition 3.3 semistandard family specialized to the canonical critical
integer orbit.

Source condition: `0 < c_k < a_k`.
The root is the cyclic conjugate of the semistandard morphism word and the
exact prefix length is

  (q_k-c_k q_(k-1))
    + Σ_{j=1}^{k} (a_j-c_j) q_(j-1).
-/
axiom bhz2006_proposition33_semistandard_critical
    (s k : ℕ)
    (hk : 1 ≤ k)
    (hDigitPos :
      0 < (CriticalBHZPhasePacket.canonical s).digit k)
    (hDigitLt :
      (CriticalBHZPhasePacket.canonical s).digit k < criticalBHZa k) :
    BHZCriticalCyclicPrefixPower
      s
      (bhzCriticalSemistandardWord
        (CriticalBHZPhasePacket.canonical s) k)
      (bhzCriticalSemistandardPowerNumerator
        (CriticalBHZPhasePacket.canonical s) k)

end ExternalArithmetic
end CSTMicro
end Collatz2
