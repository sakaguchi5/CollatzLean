import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalPrefixPowerCandidate

/-!
# BHZ Proposition 3.3: exact initial-power port

旧 `BHZCriticalInitialSquareBand` のような absolute band constant は導入しない。

BHZ Proposition 3.3 が与える source-shaped information は、phase digits `c_k`
を保持したまま、standard / semistandard primitive root に対する initial power
の長さを exact に記述すること。

repo 座標では既に

standard root:
  q_k

semistandard root:
  q_k - c_k q_(k-1)

standard maximal-prefix length numerator:
  1_{a_(k+2)=c_(k+2)} q_k
    + Σ_{j=1}^{k+1} (a_j-c_j) q_(j-1)

semistandard maximal-prefix length numerator:
  (q_k-c_k q_(k-1))
    + Σ_{j=1}^{k} (a_j-c_j) q_(j-1)

が `BHZCriticalPrefixPowerCandidate` に定義済み。

本ファイルでは、その exact length まで root-periodic であるという
Prop.3.3 の project-facing consequence だけを interface にする。
最大性そのものは Pure B では不要なので要求しない。

この port は source theorem に忠実であり、partial quotient を absolute constant に
潰さない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
shifted BHZ word の prefix `[0,length)` が root `r` を period に持つ。

`i+r < length` の範囲で bit が一致する、という直接の有限 word statement。
-/
structure CriticalShiftInitialPeriod
    (s root length : ℕ) : Prop where
  root_pos : 0 < root
  periodic :
    ∀ i : ℕ,
      i + root < length →
        criticalShiftBit s i =
          criticalShiftBit s (i + root)

namespace CriticalShiftInitialPeriod

/--
initial period が少なくとも二 root 分あれば actual Beatty square。
-/
theorem toCriticalBeattySquareAt
    {s root length : ℕ}
    (H : CriticalShiftInitialPeriod s root length)
    (hTwo : 2 * root ≤ length) :
    CriticalBeattySquareAt s root := by
  apply
    criticalBeattySquareAt_of_criticalShiftBit_blocks
      H.root_pos
  intro i hi
  have hDomain :
      i + root < length := by
    have hBeforeTwo :
        i + root < 2 * root := by
      omega
    exact lt_of_lt_of_le hBeforeTwo hTwo
  have hEq := H.periodic i hDomain
  simpa [Nat.add_comm] using hEq

end CriticalShiftInitialPeriod

/--
BHZ Proposition 3.3 の project-facing exact port。

`k >= 1` の nontrivial levels だけを使う。
semistandard family はさらに source condition

  0 < c_k < a_k

を要求する。

重要:
ここには `bandConstant`、Rhin exponent、Pure B state は一切入らない。
-/
structure BHZCriticalProposition33 where
  standard_initial_period :
    ∀ {s : ℕ}
      (P : CriticalBHZPhasePacket s)
      (k : ℕ),
      1 ≤ k →
      CriticalShiftInitialPeriod
        s
        (bhzCriticalStandardRoot k)
        (bhzCriticalStandardPowerNumerator P k)

  semistandard_initial_period :
    ∀ {s : ℕ}
      (P : CriticalBHZPhasePacket s)
      (k : ℕ),
      1 ≤ k →
      0 < P.digit k →
      P.digit k < criticalBHZa k →
      CriticalShiftInitialPeriod
        s
        (bhzCriticalSemistandardRoot P k)
        (bhzCriticalSemistandardPowerNumerator P k)

namespace BHZCriticalProposition33

/--
standard Prop.3.3 formula が square-eligible なら actual Beatty square。
-/
theorem standard_squareAt
    (B : BHZCriticalProposition33)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZStandardSquareEligible P k) :
    CriticalBeattySquareAt
      s
      (bhzCriticalStandardRoot k) := by
  have hPeriod :=
    B.standard_initial_period P k hk
  exact hPeriod.toCriticalBeattySquareAt hSquare

/--
semistandard Prop.3.3 formula が square-eligible なら actual Beatty square。
-/
theorem semistandard_squareAt
    (B : BHZCriticalProposition33)
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hSquare : BHZSemistandardSquareEligible P k) :
    CriticalBeattySquareAt
      s
      (bhzCriticalSemistandardRoot P k) := by
  have hPeriod :=
    B.semistandard_initial_period
      P k hk hSquare.1 hSquare.2.1
  exact
    hPeriod.toCriticalBeattySquareAt
      hSquare.2.2

end BHZCriticalProposition33

end ExternalArithmetic
end CSTMicro
end Collatz2
