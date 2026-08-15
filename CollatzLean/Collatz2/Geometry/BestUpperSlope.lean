import CollatzLean.Collatz2.Geometry.ContractingPairDescent

/-!
# Collatz2 Geometry: strip-reduced pair = best upper slope

Stage 1。

contracting exponent pair

  P = (p,H),   3^p < 2^H

に対し、proper denominator `0 < r < p` の最小 contracting upper depth は

  criticalHeight(r) + 1

である。

`StripReduced`

  H*r - p*criticalHeight(r) <= p

は division を使わず exact に

  H*r <= p*(criticalHeight(r)+1)

すなわち

  H/p <= (criticalHeight(r)+1)/r

と同値である。

従って `StripReduced` は「より小さい denominator の strict contracting rational は
P より critical slope に近づけない」という best-upper 性そのものである。
-/

namespace Collatz2
namespace Word
namespace ContractingExponentPair

/--
全 proper denominator の最小 contracting upper pair より slope が上に出ない。
-/
def BestUpperAtSmallerDenominators (P : ContractingExponentPair) : Prop :=
  ∀ r : ℕ,
    0 < r →
    r < P.oddCount →
    P.twoDepth * r ≤
      P.oddCount * (criticalHeight r + 1)

/--
contracting pair の rational chord は positive denominator で critical height より strict に上。
-/
theorem criticalHeight_below_chord
    (P : ContractingExponentPair)
    {r : ℕ}
    (hrPos : 0 < r) :
    P.oddCount * criticalHeight r < P.twoDepth * r := by
  have hCrit := criticalHeight_pow_lt_threePow hrPos
  have hCritRaisedRaw :=
    Nat.pow_lt_pow_left hCrit (Nat.ne_of_gt P.oddCount_pos)
  have hCritRaised :
      2 ^ (criticalHeight r * P.oddCount) <
        3 ^ (r * P.oddCount) := by
    calc
      2 ^ (criticalHeight r * P.oddCount)
          = (2 ^ criticalHeight r) ^ P.oddCount := by
              rw [pow_mul]
      _ < (3 ^ r) ^ P.oddCount := hCritRaisedRaw
      _ = 3 ^ (r * P.oddCount) := by
              rw [pow_mul]
  have hWholeRaisedRaw :=
    Nat.pow_lt_pow_left P.contracting (Nat.ne_of_gt hrPos)
  have hWholeRaised :
      3 ^ (P.oddCount * r) <
        2 ^ (P.twoDepth * r) := by
    calc
      3 ^ (P.oddCount * r)
          = (3 ^ P.oddCount) ^ r := by
              rw [pow_mul]
      _ < (2 ^ P.twoDepth) ^ r := hWholeRaisedRaw
      _ = 2 ^ (P.twoDepth * r) := by
              rw [pow_mul]
  by_contra hnot
  have hle :
      P.twoDepth * r ≤ P.oddCount * criticalHeight r := by
    omega
  have htwo :
      2 ^ (P.twoDepth * r) ≤
        2 ^ (P.oddCount * criticalHeight r) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  have hleft :
      2 ^ (P.oddCount * criticalHeight r) <
        3 ^ (P.oddCount * r) := by
    simpa [Nat.mul_comm] using hCritRaised
  have hcontra :
      2 ^ (P.twoDepth * r) <
        2 ^ (P.twoDepth * r) :=
    lt_of_le_of_lt htwo (lt_trans hleft hWholeRaised)
  exact (Nat.lt_irrefl _ hcontra)

/-- pair strip は positive denominator で strict positive。 -/
theorem stripRank_pos
    (P : ContractingExponentPair)
    {r : ℕ}
    (hrPos : 0 < r) :
    0 < P.stripRank r := by
  unfold stripRank
  exact Nat.sub_pos_of_lt (P.criticalHeight_below_chord hrPos)

/--
`StripReduced` なら smaller denominator の最小 contracting upper slope より下にある。
-/
theorem bestUpper_of_stripReduced
    {P : ContractingExponentPair}
    (hReduced : P.StripReduced) :
    P.BestUpperAtSmallerDenominators := by
  intro r hrPos hrLt
  let A := P.oddCount * criticalHeight r
  let B := P.twoDepth * r
  have hAB : A < B := by
    simpa [A, B] using P.criticalHeight_below_chord hrPos
  have hStrip : B - A ≤ P.oddCount := by
    simpa [stripRank, A, B] using hReduced r hrPos hrLt
  have hBLe : B ≤ A + P.oddCount := by
    omega
  calc
    P.twoDepth * r = B := by rfl
    _ ≤ A + P.oddCount := hBLe
    _ = P.oddCount * (criticalHeight r + 1) := by
          dsimp [A]
          ring

/--
best-upper slope 条件から `StripReduced` を回収する。
-/
theorem stripReduced_of_bestUpper
    {P : ContractingExponentPair}
    (hBest : P.BestUpperAtSmallerDenominators) :
    P.StripReduced := by
  intro r hrPos hrLt
  let A := P.oddCount * criticalHeight r
  let B := P.twoDepth * r
  have hAB : A < B := by
    simpa [A, B] using P.criticalHeight_below_chord hrPos
  have hBest' : B ≤ A + P.oddCount := by
    have h := hBest r hrPos hrLt
    simpa [A, B, Nat.mul_add] using h
  have hSub : B - A ≤ P.oddCount := by
    omega
  simpa [stripRank, A, B] using hSub

/-- Stage 1 の exact equivalence。 -/
theorem stripReduced_iff_bestUpper
    (P : ContractingExponentPair) :
    P.StripReduced ↔ P.BestUpperAtSmallerDenominators := by
  constructor
  · exact bestUpper_of_stripReduced
  · exact stripReduced_of_bestUpper

/--
Best-upper 性を既存の cross-product slope order で読む。
-/
theorem stripReduced_iff_slopeBelow_criticalUpper
    (P : ContractingExponentPair) :
    P.StripReduced ↔
      ∀ r : ℕ,
        ∀ hrPos : 0 < r,
        r < P.oddCount →
        SlopeBelow P (criticalUpperPair r hrPos) := by
  rw [stripReduced_iff_bestUpper]
  constructor
  · intro h r hrPos hrLt
    have hBest := h r hrPos hrLt
    simpa [SlopeBelow,mul_comm] using hBest
  · intro h r hrPos hrLt
    have hSlope := h r hrPos hrLt
    simpa [SlopeBelow,mul_comm] using hSlope

end ContractingExponentPair
end Word
end Collatz2
