import CollatzLean.Collatz2.Geometry.RankStrip

/-!
# Collatz2 Geometry: wide-strip denominator descent

Stage 9a / 9b。

word から一度離れ、contracting exponent pair

  3^p < 2^H

だけを保持する。

critical height

  c(r) = max { h | 2^h < 3^r }

に対し

  strip(P,r) = H*r - p*c(r)

と置く。もし proper denominator `0 < r < p` で

  p < strip(P,r)

なら

  p * (c(r)+1) < H*r

であり、

  Q = (r, c(r)+1)

は strict contracting かつ P より小さい slope を持つ。
したがって denominator は strict に減る。

この降下を strong induction で反復し、最終的に

  strip(Q,r) <= Q.p

を全 proper r で満たす reduced / best-upper pair を得る。
-/

namespace Collatz2
namespace Word

/-- `3^p < 2^H` を保持する純 exponent pair。 -/
structure ContractingExponentPair where
  oddCount : ℕ
  twoDepth : ℕ
  oddCount_pos : 0 < oddCount
  contracting : 3 ^ oddCount < 2 ^ twoDepth

namespace ContractingExponentPair

/-- pair の rational chord と critical line の rank-width。 -/
def stripRank (P : ContractingExponentPair) (r : ℕ) : ℕ :=
  P.twoDepth * r - P.oddCount * criticalHeight r

/-- `Q` の slope `H_Q/p_Q` が `P` 以下。division を使わない cross-product 版。 -/
def SlopeBelow (Q P : ContractingExponentPair) : Prop :=
  Q.twoDepth * P.oddCount ≤ P.twoDepth * Q.oddCount

/-- strict slope descent。 -/
def SlopeStrictBelow (Q P : ContractingExponentPair) : Prop :=
  Q.twoDepth * P.oddCount < P.twoDepth * Q.oddCount

/-- proper denominator に wide strip が存在する。 -/
def HasWideStrip (P : ContractingExponentPair) : Prop :=
  ∃ r : ℕ,
    0 < r ∧
    r < P.oddCount ∧
    P.oddCount < P.stripRank r

/-- 全 proper denominator の strip width が `p` 以下。 -/
def StripReduced (P : ContractingExponentPair) : Prop :=
  ∀ r : ℕ,
    0 < r →
    r < P.oddCount →
    P.stripRank r ≤ P.oddCount

/-- slope の reflexivity。 -/
theorem slopeBelow_refl (P : ContractingExponentPair) :
    SlopeBelow P P := by
  unfold SlopeBelow
  exact le_rfl

/-- slope cross-product ordering は transitive。 -/
theorem slopeBelow_trans
    {P Q R : ContractingExponentPair}
    (hPQ : SlopeBelow P Q)
    (hQR : SlopeBelow Q R) :
    SlopeBelow P R := by
  unfold SlopeBelow at hPQ hQR ⊢
  have hscaled :
      Q.oddCount * (P.twoDepth * R.oddCount) ≤
        Q.oddCount * (R.twoDepth * P.oddCount) := by
    calc
      Q.oddCount * (P.twoDepth * R.oddCount)
          = (P.twoDepth * Q.oddCount) * R.oddCount := by ring
      _ ≤ (Q.twoDepth * P.oddCount) * R.oddCount :=
        Nat.mul_le_mul_right R.oddCount hPQ
      _ = P.oddCount * (Q.twoDepth * R.oddCount) := by ring
      _ ≤ P.oddCount * (R.twoDepth * Q.oddCount) :=
        Nat.mul_le_mul_left P.oddCount hQR
      _ = Q.oddCount * (R.twoDepth * P.oddCount) := by ring
  by_contra hnot
  have hrev :
      R.twoDepth * P.oddCount < P.twoDepth * R.oddCount := by
    omega
  have hrevScaled :
      Q.oddCount * (R.twoDepth * P.oddCount) <
        Q.oddCount * (P.twoDepth * R.oddCount) :=
    (Nat.mul_lt_mul_left Q.oddCount_pos).2 hrev
  exact (not_lt_of_ge hscaled) hrevScaled

/-- strict slope descent は weak descent でもある。 -/
theorem slopeBelow_of_strict
    {P Q : ContractingExponentPair}
    (h : SlopeStrictBelow Q P) :
    SlopeBelow Q P := by
  unfold SlopeStrictBelow at h
  unfold SlopeBelow
  exact Nat.le_of_lt h

/-- `HasWideStrip` がなければ reduced。 -/
theorem stripReduced_of_not_hasWideStrip
    {P : ContractingExponentPair}
    (hnot : ¬ P.HasWideStrip) :
    P.StripReduced := by
  intro r hrPos hrLt
  by_contra hnotLe
  have hWide : P.oddCount < P.stripRank r := by omega
  exact hnot ⟨r, hrPos, hrLt, hWide⟩

/--
critical height の直上 `(r, criticalHeight r + 1)` は strict contracting。
-/
def criticalUpperPair
    (r : ℕ)
    (hrPos : 0 < r) : ContractingExponentPair := by
  let c := criticalHeight r
  have hLog :
      3 ^ r - 1 < 2 ^ (c + 1) := by
    dsimp [c, criticalHeight]
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) (3 ^ r - 1)
  have hLe :
      3 ^ r ≤ 2 ^ (c + 1) := by
    omega
  have hNe :
      3 ^ r ≠ 2 ^ (c + 1) := by
    intro hEq
    have hOdd : Odd (3 ^ r) :=
      (show Odd (3 : ℕ) by decide).pow
    rcases hOdd with ⟨a, ha⟩
    have hEven :
        ∃ b : ℕ, 2 ^ (c + 1) = 2 * b := by
      refine ⟨2 ^ c, ?_⟩
      rw [pow_succ]
      ring
    rcases hEven with ⟨b, hb⟩
    rw [ha, hb] at hEq
    omega
  exact {
    oddCount := r
    twoDepth := c + 1
    oddCount_pos := hrPos
    contracting := lt_of_le_of_ne hLe hNe
  }

@[simp] theorem criticalUpperPair_oddCount
    (r : ℕ)
    (hrPos : 0 < r) :
    (criticalUpperPair r hrPos).oddCount = r := rfl

@[simp] theorem criticalUpperPair_twoDepth
    (r : ℕ)
    (hrPos : 0 < r) :
    (criticalUpperPair r hrPos).twoDepth = criticalHeight r + 1 := rfl

/--
wide strip は critical-upper pair の strict slope descent を与える。

  p < H*r - p*c
  => p*(c+1) < H*r.
-/
theorem criticalUpperPair_strictBelow_of_wide
    {P : ContractingExponentPair}
    {r : ℕ}
    (hrPos : 0 < r)
    (hWide : P.oddCount < P.stripRank r) :
    SlopeStrictBelow (criticalUpperPair r hrPos) P := by
  let c := criticalHeight r
  let A := P.oddCount * c
  let B := P.twoDepth * r
  have hWide' : P.oddCount < B - A := by
    simpa [stripRank, c, A, B] using hWide
  have hDiffPos : 0 < B - A :=
    lt_trans P.oddCount_pos hWide'
  have hAB : A < B :=
    Nat.sub_pos_iff_lt.mp hDiffPos
  have hAdd : A + P.oddCount < B := by
    omega
  have hCross :
      (criticalHeight r + 1) * P.oddCount <
        P.twoDepth * r := by
    calc
      (criticalHeight r + 1) * P.oddCount
          = A + P.oddCount := by
              dsimp [A, c]
              ring
      _ < B := hAdd
      _ = P.twoDepth * r := by rfl
  simpa [SlopeStrictBelow] using hCross

/--
9a: wide strip から denominator が strict に小さい contracting pair を得る。
-/
theorem exists_smaller_contractingPair_of_wide
    {P : ContractingExponentPair}
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount)
    (hWide : P.oddCount < P.stripRank r) :
    ∃ Q : ContractingExponentPair,
      Q.oddCount < P.oddCount ∧
      SlopeStrictBelow Q P := by
  let Q := criticalUpperPair r hrPos
  refine ⟨Q, ?_, ?_⟩
  · simpa [Q] using hrLt
  · simpa [Q] using
      criticalUpperPair_strictBelow_of_wide hrPos hWide

/-- reduced descendant packet。 -/
structure BestUpperCertificate (P : ContractingExponentPair) where
  pair : ContractingExponentPair
  reduced : pair.StripReduced
  slope_below : SlopeBelow pair P
  denominator_le : pair.oddCount ≤ P.oddCount

/--
strong induction 用内部定理。
任意 pair は denominator を増やさず reduced descendant へ降下できる。
-/
private theorem exists_bestUpperCertificate_aux
    (p : ℕ) :
    ∀ P : ContractingExponentPair,
      P.oddCount = p →
      Nonempty (BestUpperCertificate P) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
      intro P hp
      by_cases hWide : P.HasWideStrip
      · rcases hWide with ⟨r, hrPos, hrLtP, hrWide⟩
        let Q := criticalUpperPair r hrPos
        have hQodd : Q.oddCount = r := by
          rfl
        have hrLt : r < p := by
          rw [← hp]
          exact hrLtP
        obtain ⟨Cq⟩ := ih r hrLt Q hQodd
        have hQPstrict : SlopeStrictBelow Q P := by
          simpa [Q] using
            criticalUpperPair_strictBelow_of_wide hrPos hrWide
        have hQP : SlopeBelow Q P :=
          slopeBelow_of_strict hQPstrict
        let C : BestUpperCertificate P := {
          pair := Cq.pair
          reduced := Cq.reduced
          slope_below := slopeBelow_trans Cq.slope_below hQP
          denominator_le := by
            calc
              Cq.pair.oddCount ≤ Q.oddCount := Cq.denominator_le
              _ = r := rfl
              _ ≤ P.oddCount := Nat.le_of_lt hrLtP
        }
        exact ⟨C⟩
      · let C : BestUpperCertificate P := {
          pair := P
          reduced := stripReduced_of_not_hasWideStrip hWide
          slope_below := slopeBelow_refl P
          denominator_le := le_rfl
        }
        exact ⟨C⟩

/--
9b: finite denominator descent の終点。
任意 contracting pair は slope を上げずに `StripReduced` pair へ到達する。
-/
theorem exists_bestUpperCertificate
    (P : ContractingExponentPair) :
    Nonempty (BestUpperCertificate P) := by
  exact exists_bestUpperCertificate_aux P.oddCount P rfl

/-- wide strip が初手にあれば最終 denominator も strict に小さく取れる。 -/
theorem exists_bestUpperCertificate_strict_of_wide
    {P : ContractingExponentPair}
    (hWide : P.HasWideStrip) :
    ∃ C : BestUpperCertificate P,
      C.pair.oddCount < P.oddCount := by
  rcases hWide with ⟨r, hrPos, hrLt, hRank⟩
  let Q := criticalUpperPair r hrPos
  obtain ⟨Cq⟩ := exists_bestUpperCertificate Q
  have hQPstrict : SlopeStrictBelow Q P := by
    simpa [Q] using
      criticalUpperPair_strictBelow_of_wide hrPos hRank
  have hQP : SlopeBelow Q P := slopeBelow_of_strict hQPstrict
  let C : BestUpperCertificate P := {
    pair := Cq.pair
    reduced := Cq.reduced
    slope_below := slopeBelow_trans Cq.slope_below hQP
    denominator_le := by
      calc
        Cq.pair.oddCount ≤ Q.oddCount := Cq.denominator_le
        _ = r := rfl
        _ ≤ P.oddCount := Nat.le_of_lt hrLt
  }
  refine ⟨C, ?_⟩
  dsimp [C]
  exact lt_of_le_of_lt Cq.denominator_le (by simpa [Q] using hrLt)

end ContractingExponentPair
end Word
end Collatz2
